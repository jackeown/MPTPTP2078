%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Hg5UkFaEgW

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   58 (  84 expanded)
%              Number of leaves         :   21 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :  389 ( 907 expanded)
%              Number of equality atoms :   18 (  42 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v4_relat_1 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v4_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('7',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['4','7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ sk_C ) )
    | ( sk_B
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D )
       => ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) )
          & ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ X14 ) @ X15 )
      | ( r1_tarski @ X14 @ ( k1_relset_1 @ X16 @ X17 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t30_relset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ ( k6_relat_1 @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('16',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('17',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_C ) )
      | ~ ( r1_tarski @ ( k6_relat_1 @ X0 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
    r1_tarski @ sk_B @ ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['10','19'])).

thf('21',plain,
    ( ( sk_B
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ~ ( r1_tarski @ sk_B @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( sk_B
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( sk_B
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('24',plain,
    ( ( sk_B
     != ( k1_relat_1 @ sk_C ) )
   <= ( sk_B
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ X14 ) @ X15 )
      | ( r1_tarski @ X14 @ ( k2_relset_1 @ X16 @ X17 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t30_relset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ ( k6_relat_1 @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ sk_B @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ~ ( r1_tarski @ sk_B @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['21'])).

thf('31',plain,(
    r1_tarski @ sk_B @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_B
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ~ ( r1_tarski @ sk_B @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['21'])).

thf('33',plain,(
    sk_B
 != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['31','32'])).

thf('34',plain,(
    sk_B
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['24','33'])).

thf('35',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['20','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Hg5UkFaEgW
% 0.13/0.36  % Computer   : n007.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 18:03:51 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 32 iterations in 0.018s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.50  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.50  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.22/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.22/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.50  thf(t31_relset_1, conjecture,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.22/0.50       ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C ) =>
% 0.22/0.50         ( ( ( B ) = ( k1_relset_1 @ B @ A @ C ) ) & 
% 0.22/0.50           ( r1_tarski @ B @ ( k2_relset_1 @ B @ A @ C ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.50        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.22/0.50          ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C ) =>
% 0.22/0.50            ( ( ( B ) = ( k1_relset_1 @ B @ A @ C ) ) & 
% 0.22/0.50              ( r1_tarski @ B @ ( k2_relset_1 @ B @ A @ C ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t31_relset_1])).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(cc2_relset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.50       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.50         ((v4_relat_1 @ X8 @ X9)
% 0.22/0.50          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.50  thf('2', plain, ((v4_relat_1 @ sk_C @ sk_B)),
% 0.22/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.50  thf(d18_relat_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ B ) =>
% 0.22/0.50       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (![X3 : $i, X4 : $i]:
% 0.22/0.50         (~ (v4_relat_1 @ X3 @ X4)
% 0.22/0.50          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 0.22/0.50          | ~ (v1_relat_1 @ X3))),
% 0.22/0.50      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(cc1_relset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.50       ( v1_relat_1 @ C ) ))).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.50         ((v1_relat_1 @ X5)
% 0.22/0.50          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.50  thf('7', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf('8', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_B)),
% 0.22/0.50      inference('demod', [status(thm)], ['4', '7'])).
% 0.22/0.50  thf(d10_xboole_0, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (![X0 : $i, X2 : $i]:
% 0.22/0.50         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ sk_C))
% 0.22/0.50        | ((sk_B) = (k1_relat_1 @ sk_C)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.50  thf('11', plain, ((r1_tarski @ (k6_relat_1 @ sk_B) @ sk_C)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t30_relset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.50       ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D ) =>
% 0.22/0.50         ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) ) & 
% 0.22/0.50           ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.50         (~ (r1_tarski @ (k6_relat_1 @ X14) @ X15)
% 0.22/0.50          | (r1_tarski @ X14 @ (k1_relset_1 @ X16 @ X17 @ X15))
% 0.22/0.50          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.22/0.50      inference('cnf', [status(esa)], [t30_relset_1])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((r1_tarski @ X0 @ (k1_relset_1 @ sk_B @ sk_A @ sk_C))
% 0.22/0.50          | ~ (r1_tarski @ (k6_relat_1 @ X0) @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(redefinition_k1_relset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.50       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.50         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 0.22/0.50          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((r1_tarski @ X0 @ (k1_relat_1 @ sk_C))
% 0.22/0.50          | ~ (r1_tarski @ (k6_relat_1 @ X0) @ sk_C))),
% 0.22/0.50      inference('demod', [status(thm)], ['14', '17'])).
% 0.22/0.50  thf('19', plain, ((r1_tarski @ sk_B @ (k1_relat_1 @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['11', '18'])).
% 0.22/0.50  thf('20', plain, (((sk_B) = (k1_relat_1 @ sk_C))),
% 0.22/0.50      inference('demod', [status(thm)], ['10', '19'])).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      ((((sk_B) != (k1_relset_1 @ sk_B @ sk_A @ sk_C))
% 0.22/0.50        | ~ (r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      ((((sk_B) != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.22/0.50         <= (~ (((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.22/0.50      inference('split', [status(esa)], ['21'])).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      ((((sk_B) != (k1_relat_1 @ sk_C)))
% 0.22/0.50         <= (~ (((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.22/0.50      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.50  thf('25', plain, ((r1_tarski @ (k6_relat_1 @ sk_B) @ sk_C)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.50         (~ (r1_tarski @ (k6_relat_1 @ X14) @ X15)
% 0.22/0.50          | (r1_tarski @ X14 @ (k2_relset_1 @ X16 @ X17 @ X15))
% 0.22/0.50          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.22/0.50      inference('cnf', [status(esa)], [t30_relset_1])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((r1_tarski @ X0 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))
% 0.22/0.50          | ~ (r1_tarski @ (k6_relat_1 @ X0) @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.50  thf('29', plain, ((r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['25', '28'])).
% 0.22/0.50  thf('30', plain,
% 0.22/0.50      ((~ (r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.22/0.50         <= (~ ((r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.22/0.50      inference('split', [status(esa)], ['21'])).
% 0.22/0.50  thf('31', plain, (((r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.50  thf('32', plain,
% 0.22/0.50      (~ (((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_C))) | 
% 0.22/0.50       ~ ((r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.22/0.50      inference('split', [status(esa)], ['21'])).
% 0.22/0.50  thf('33', plain, (~ (((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['31', '32'])).
% 0.22/0.50  thf('34', plain, (((sk_B) != (k1_relat_1 @ sk_C))),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['24', '33'])).
% 0.22/0.50  thf('35', plain, ($false),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['20', '34'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
