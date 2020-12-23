%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1vcLlmprhb

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 108 expanded)
%              Number of leaves         :   27 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :  418 ( 639 expanded)
%              Number of equality atoms :   44 (  81 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t171_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t171_funct_2])).

thf('0',plain,(
    ( k8_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('1',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( ( k8_relset_1 @ X15 @ X16 @ X14 @ X17 )
        = ( k10_relat_1 @ X14 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X13 ) @ ( k6_relat_1 @ X12 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X20: $i] :
      ( ( k6_partfun1 @ X20 )
      = ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('6',plain,(
    ! [X20: $i] :
      ( ( k6_partfun1 @ X20 )
      = ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('7',plain,(
    ! [X20: $i] :
      ( ( k6_partfun1 @ X20 )
      = ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X13 ) @ ( k6_partfun1 @ X12 ) )
      = ( k6_partfun1 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k10_relat_1 @ X7 @ ( k1_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k6_partfun1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k1_relat_1 @ ( k6_partfun1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('11',plain,(
    ! [X8: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('12',plain,(
    ! [X20: $i] :
      ( ( k6_partfun1 @ X20 )
      = ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('13',plain,(
    ! [X8: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X8 ) )
      = X8 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X8: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X8 ) )
      = X8 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('15',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('16',plain,(
    ! [X20: $i] :
      ( ( k6_partfun1 @ X20 )
      = ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('17',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X5 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X5 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['10','13','14','17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X9: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('25',plain,(
    ! [X20: $i] :
      ( ( k6_partfun1 @ X20 )
      = ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X9: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X9 ) )
      = X9 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('27',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ( ( k5_relat_1 @ X10 @ ( k6_relat_1 @ X11 ) )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('28',plain,(
    ! [X20: $i] :
      ( ( k6_partfun1 @ X20 )
      = ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('29',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ( ( k5_relat_1 @ X10 @ ( k6_partfun1 @ X11 ) )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X1 ) )
        = ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X5 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('32',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X13 ) @ ( k6_partfun1 @ X12 ) )
      = ( k6_partfun1 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k6_partfun1 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ( k6_partfun1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference('sup-',[status(thm)],['23','33'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,
    ( ( k6_partfun1 @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X8: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X8 ) )
      = X8 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('38',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X8: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X8 ) )
      = X8 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('40',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    sk_B != sk_B ),
    inference(demod,[status(thm)],['0','20','40'])).

thf('42',plain,(
    $false ),
    inference(simplify,[status(thm)],['41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1vcLlmprhb
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:09:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 27 iterations in 0.016s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.47  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.21/0.47  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.47  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.47  thf(t171_funct_2, conjecture,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47       ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i]:
% 0.21/0.47        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47          ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t171_funct_2])).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      (((k8_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ sk_B) != (sk_B))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(dt_k6_partfun1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( m1_subset_1 @
% 0.21/0.47         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.21/0.47       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X19 : $i]:
% 0.21/0.47         (m1_subset_1 @ (k6_partfun1 @ X19) @ 
% 0.21/0.47          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.21/0.47  thf(redefinition_k8_relset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.47       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.21/0.47          | ((k8_relset_1 @ X15 @ X16 @ X14 @ X17) = (k10_relat_1 @ X14 @ X17)))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((k8_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 0.21/0.47           = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf(t43_funct_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.21/0.47       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X12 : $i, X13 : $i]:
% 0.21/0.47         ((k5_relat_1 @ (k6_relat_1 @ X13) @ (k6_relat_1 @ X12))
% 0.21/0.47           = (k6_relat_1 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.21/0.47  thf(redefinition_k6_partfun1, axiom,
% 0.21/0.47    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.21/0.47  thf('5', plain, (![X20 : $i]: ((k6_partfun1 @ X20) = (k6_relat_1 @ X20))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.47  thf('6', plain, (![X20 : $i]: ((k6_partfun1 @ X20) = (k6_relat_1 @ X20))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.47  thf('7', plain, (![X20 : $i]: ((k6_partfun1 @ X20) = (k6_relat_1 @ X20))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X12 : $i, X13 : $i]:
% 0.21/0.47         ((k5_relat_1 @ (k6_partfun1 @ X13) @ (k6_partfun1 @ X12))
% 0.21/0.47           = (k6_partfun1 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.21/0.47      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.21/0.47  thf(t182_relat_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( v1_relat_1 @ B ) =>
% 0.21/0.47           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.21/0.47             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X6 : $i, X7 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X6)
% 0.21/0.47          | ((k1_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 0.21/0.47              = (k10_relat_1 @ X7 @ (k1_relat_1 @ X6)))
% 0.21/0.47          | ~ (v1_relat_1 @ X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (((k1_relat_1 @ (k6_partfun1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.21/0.47            = (k10_relat_1 @ (k6_partfun1 @ X0) @ 
% 0.21/0.47               (k1_relat_1 @ (k6_partfun1 @ X1))))
% 0.21/0.47          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.21/0.47          | ~ (v1_relat_1 @ (k6_partfun1 @ X1)))),
% 0.21/0.47      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf(t71_relat_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.47       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.47  thf('11', plain, (![X8 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.47  thf('12', plain, (![X20 : $i]: ((k6_partfun1 @ X20) = (k6_relat_1 @ X20))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.47  thf('13', plain, (![X8 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X8)) = (X8))),
% 0.21/0.47      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.47  thf('14', plain, (![X8 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X8)) = (X8))),
% 0.21/0.47      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.47  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.21/0.47  thf('15', plain, (![X5 : $i]: (v1_relat_1 @ (k6_relat_1 @ X5))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.47  thf('16', plain, (![X20 : $i]: ((k6_partfun1 @ X20) = (k6_relat_1 @ X20))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.47  thf('17', plain, (![X5 : $i]: (v1_relat_1 @ (k6_partfun1 @ X5))),
% 0.21/0.47      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.47  thf('18', plain, (![X5 : $i]: (v1_relat_1 @ (k6_partfun1 @ X5))),
% 0.21/0.47      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((k3_xboole_0 @ X1 @ X0) = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.21/0.47      inference('demod', [status(thm)], ['10', '13', '14', '17', '18'])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((k8_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 0.21/0.47           = (k3_xboole_0 @ X1 @ X0))),
% 0.21/0.47      inference('demod', [status(thm)], ['3', '19'])).
% 0.21/0.47  thf('21', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t3_subset, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      (![X2 : $i, X3 : $i]:
% 0.21/0.47         ((r1_tarski @ X2 @ X3) | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.47  thf('23', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.21/0.47      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.47  thf('24', plain, (![X9 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 0.21/0.47      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.47  thf('25', plain, (![X20 : $i]: ((k6_partfun1 @ X20) = (k6_relat_1 @ X20))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.47  thf('26', plain, (![X9 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X9)) = (X9))),
% 0.21/0.47      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.47  thf(t79_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ B ) =>
% 0.21/0.47       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.21/0.47         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.21/0.47  thf('27', plain,
% 0.21/0.47      (![X10 : $i, X11 : $i]:
% 0.21/0.47         (~ (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 0.21/0.47          | ((k5_relat_1 @ X10 @ (k6_relat_1 @ X11)) = (X10))
% 0.21/0.47          | ~ (v1_relat_1 @ X10))),
% 0.21/0.47      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.21/0.47  thf('28', plain, (![X20 : $i]: ((k6_partfun1 @ X20) = (k6_relat_1 @ X20))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.47  thf('29', plain,
% 0.21/0.47      (![X10 : $i, X11 : $i]:
% 0.21/0.47         (~ (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 0.21/0.47          | ((k5_relat_1 @ X10 @ (k6_partfun1 @ X11)) = (X10))
% 0.21/0.47          | ~ (v1_relat_1 @ X10))),
% 0.21/0.47      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.47  thf('30', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.47          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.21/0.47          | ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X1))
% 0.21/0.47              = (k6_partfun1 @ X0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['26', '29'])).
% 0.21/0.47  thf('31', plain, (![X5 : $i]: (v1_relat_1 @ (k6_partfun1 @ X5))),
% 0.21/0.47      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.47  thf('32', plain,
% 0.21/0.47      (![X12 : $i, X13 : $i]:
% 0.21/0.47         ((k5_relat_1 @ (k6_partfun1 @ X13) @ (k6_partfun1 @ X12))
% 0.21/0.47           = (k6_partfun1 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.21/0.47      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.21/0.47  thf('33', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.47          | ((k6_partfun1 @ (k3_xboole_0 @ X1 @ X0)) = (k6_partfun1 @ X0)))),
% 0.21/0.47      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.21/0.47  thf('34', plain,
% 0.21/0.47      (((k6_partfun1 @ (k3_xboole_0 @ sk_A @ sk_B)) = (k6_partfun1 @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['23', '33'])).
% 0.21/0.47  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.47  thf('35', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.47  thf('36', plain,
% 0.21/0.47      (((k6_partfun1 @ (k3_xboole_0 @ sk_B @ sk_A)) = (k6_partfun1 @ sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.47  thf('37', plain, (![X8 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X8)) = (X8))),
% 0.21/0.47      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.47  thf('38', plain,
% 0.21/0.47      (((k1_relat_1 @ (k6_partfun1 @ sk_B)) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.47      inference('sup+', [status(thm)], ['36', '37'])).
% 0.21/0.47  thf('39', plain, (![X8 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X8)) = (X8))),
% 0.21/0.47      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.47  thf('40', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.47  thf('41', plain, (((sk_B) != (sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['0', '20', '40'])).
% 0.21/0.47  thf('42', plain, ($false), inference('simplify', [status(thm)], ['41'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
