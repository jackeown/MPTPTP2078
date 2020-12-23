%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HT3eQZeCKy

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:31 EST 2020

% Result     : Theorem 1.03s
% Output     : Refutation 1.03s
% Verified   : 
% Statistics : Number of formulae       :   80 (  95 expanded)
%              Number of leaves         :   35 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :  438 ( 528 expanded)
%              Number of equality atoms :   38 (  52 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('1',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('4',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( ( k8_relset_1 @ X35 @ X36 @ X34 @ X37 )
        = ( k10_relat_1 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ( k10_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(demod,[status(thm)],['0','5'])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X33 ) @ ( k6_relat_1 @ X32 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('8',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('9',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('10',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('11',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X33 ) @ ( k6_partfun1 @ X32 ) )
      = ( k6_partfun1 @ ( k3_xboole_0 @ X32 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('12',plain,(
    ! [X30: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('13',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('14',plain,(
    ! [X30: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X30 ) )
      = X30 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('15',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X29 @ X28 ) )
        = ( k10_relat_1 @ X29 @ ( k1_relat_1 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('17',plain,(
    ! [X27: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('18',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('19',plain,(
    ! [X27: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X27 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k6_partfun1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','20'])).

thf('22',plain,(
    ! [X30: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X30 ) )
      = X30 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('23',plain,(
    ! [X27: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X27 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('28',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('29',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('32',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('36',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('37',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('38',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,(
    sk_B != sk_B ),
    inference(demod,[status(thm)],['6','24','41'])).

thf('43',plain,(
    $false ),
    inference(simplify,[status(thm)],['42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HT3eQZeCKy
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:00:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.03/1.22  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.03/1.22  % Solved by: fo/fo7.sh
% 1.03/1.22  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.03/1.22  % done 2192 iterations in 0.771s
% 1.03/1.22  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.03/1.22  % SZS output start Refutation
% 1.03/1.22  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.03/1.22  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.03/1.22  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.03/1.22  thf(sk_A_type, type, sk_A: $i).
% 1.03/1.22  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.03/1.22  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.03/1.22  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.03/1.22  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.03/1.22  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.03/1.22  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.03/1.22  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.03/1.22  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.03/1.22  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.03/1.22  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 1.03/1.22  thf(sk_B_type, type, sk_B: $i).
% 1.03/1.22  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.03/1.22  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.03/1.22  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.03/1.22  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.03/1.22  thf(t171_funct_2, conjecture,
% 1.03/1.22    (![A:$i,B:$i]:
% 1.03/1.22     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.03/1.22       ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ))).
% 1.03/1.22  thf(zf_stmt_0, negated_conjecture,
% 1.03/1.22    (~( ![A:$i,B:$i]:
% 1.03/1.22        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.03/1.22          ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ) )),
% 1.03/1.22    inference('cnf.neg', [status(esa)], [t171_funct_2])).
% 1.03/1.22  thf('0', plain,
% 1.03/1.22      (((k8_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ sk_B) != (sk_B))),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf(t29_relset_1, axiom,
% 1.03/1.22    (![A:$i]:
% 1.03/1.22     ( m1_subset_1 @
% 1.03/1.22       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.03/1.22  thf('1', plain,
% 1.03/1.22      (![X38 : $i]:
% 1.03/1.22         (m1_subset_1 @ (k6_relat_1 @ X38) @ 
% 1.03/1.22          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X38)))),
% 1.03/1.22      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.03/1.22  thf(redefinition_k6_partfun1, axiom,
% 1.03/1.22    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.03/1.22  thf('2', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 1.03/1.22      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.03/1.22  thf('3', plain,
% 1.03/1.22      (![X38 : $i]:
% 1.03/1.22         (m1_subset_1 @ (k6_partfun1 @ X38) @ 
% 1.03/1.22          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X38)))),
% 1.03/1.22      inference('demod', [status(thm)], ['1', '2'])).
% 1.03/1.22  thf(redefinition_k8_relset_1, axiom,
% 1.03/1.22    (![A:$i,B:$i,C:$i,D:$i]:
% 1.03/1.22     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.22       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 1.03/1.22  thf('4', plain,
% 1.03/1.22      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 1.03/1.22         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 1.03/1.22          | ((k8_relset_1 @ X35 @ X36 @ X34 @ X37) = (k10_relat_1 @ X34 @ X37)))),
% 1.03/1.22      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 1.03/1.22  thf('5', plain,
% 1.03/1.22      (![X0 : $i, X1 : $i]:
% 1.03/1.22         ((k8_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 1.03/1.22           = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 1.03/1.22      inference('sup-', [status(thm)], ['3', '4'])).
% 1.03/1.22  thf('6', plain, (((k10_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B) != (sk_B))),
% 1.03/1.22      inference('demod', [status(thm)], ['0', '5'])).
% 1.03/1.22  thf(t43_funct_1, axiom,
% 1.03/1.22    (![A:$i,B:$i]:
% 1.03/1.22     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 1.03/1.22       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.03/1.22  thf('7', plain,
% 1.03/1.22      (![X32 : $i, X33 : $i]:
% 1.03/1.22         ((k5_relat_1 @ (k6_relat_1 @ X33) @ (k6_relat_1 @ X32))
% 1.03/1.22           = (k6_relat_1 @ (k3_xboole_0 @ X32 @ X33)))),
% 1.03/1.22      inference('cnf', [status(esa)], [t43_funct_1])).
% 1.03/1.22  thf('8', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 1.03/1.22      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.03/1.22  thf('9', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 1.03/1.22      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.03/1.22  thf('10', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 1.03/1.22      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.03/1.22  thf('11', plain,
% 1.03/1.22      (![X32 : $i, X33 : $i]:
% 1.03/1.22         ((k5_relat_1 @ (k6_partfun1 @ X33) @ (k6_partfun1 @ X32))
% 1.03/1.22           = (k6_partfun1 @ (k3_xboole_0 @ X32 @ X33)))),
% 1.03/1.22      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 1.03/1.22  thf(t71_relat_1, axiom,
% 1.03/1.22    (![A:$i]:
% 1.03/1.22     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.03/1.22       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.03/1.22  thf('12', plain, (![X30 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X30)) = (X30))),
% 1.03/1.22      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.03/1.22  thf('13', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 1.03/1.22      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.03/1.22  thf('14', plain, (![X30 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X30)) = (X30))),
% 1.03/1.22      inference('demod', [status(thm)], ['12', '13'])).
% 1.03/1.22  thf(t182_relat_1, axiom,
% 1.03/1.22    (![A:$i]:
% 1.03/1.22     ( ( v1_relat_1 @ A ) =>
% 1.03/1.22       ( ![B:$i]:
% 1.03/1.22         ( ( v1_relat_1 @ B ) =>
% 1.03/1.22           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.03/1.22             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 1.03/1.22  thf('15', plain,
% 1.03/1.22      (![X28 : $i, X29 : $i]:
% 1.03/1.22         (~ (v1_relat_1 @ X28)
% 1.03/1.22          | ((k1_relat_1 @ (k5_relat_1 @ X29 @ X28))
% 1.03/1.22              = (k10_relat_1 @ X29 @ (k1_relat_1 @ X28)))
% 1.03/1.22          | ~ (v1_relat_1 @ X29))),
% 1.03/1.22      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.03/1.22  thf('16', plain,
% 1.03/1.22      (![X0 : $i, X1 : $i]:
% 1.03/1.22         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 1.03/1.22            = (k10_relat_1 @ X1 @ X0))
% 1.03/1.22          | ~ (v1_relat_1 @ X1)
% 1.03/1.22          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 1.03/1.22      inference('sup+', [status(thm)], ['14', '15'])).
% 1.03/1.22  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 1.03/1.22  thf('17', plain, (![X27 : $i]: (v1_relat_1 @ (k6_relat_1 @ X27))),
% 1.03/1.22      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.03/1.22  thf('18', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 1.03/1.22      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.03/1.22  thf('19', plain, (![X27 : $i]: (v1_relat_1 @ (k6_partfun1 @ X27))),
% 1.03/1.22      inference('demod', [status(thm)], ['17', '18'])).
% 1.03/1.22  thf('20', plain,
% 1.03/1.22      (![X0 : $i, X1 : $i]:
% 1.03/1.22         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 1.03/1.22            = (k10_relat_1 @ X1 @ X0))
% 1.03/1.22          | ~ (v1_relat_1 @ X1))),
% 1.03/1.22      inference('demod', [status(thm)], ['16', '19'])).
% 1.03/1.22  thf('21', plain,
% 1.03/1.22      (![X0 : $i, X1 : $i]:
% 1.03/1.22         (((k1_relat_1 @ (k6_partfun1 @ (k3_xboole_0 @ X1 @ X0)))
% 1.03/1.22            = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 1.03/1.22          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 1.03/1.22      inference('sup+', [status(thm)], ['11', '20'])).
% 1.03/1.22  thf('22', plain, (![X30 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X30)) = (X30))),
% 1.03/1.22      inference('demod', [status(thm)], ['12', '13'])).
% 1.03/1.22  thf('23', plain, (![X27 : $i]: (v1_relat_1 @ (k6_partfun1 @ X27))),
% 1.03/1.22      inference('demod', [status(thm)], ['17', '18'])).
% 1.03/1.22  thf('24', plain,
% 1.03/1.22      (![X0 : $i, X1 : $i]:
% 1.03/1.22         ((k3_xboole_0 @ X1 @ X0) = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 1.03/1.22      inference('demod', [status(thm)], ['21', '22', '23'])).
% 1.03/1.22  thf('25', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.03/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.22  thf(t3_subset, axiom,
% 1.03/1.22    (![A:$i,B:$i]:
% 1.03/1.22     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.03/1.22  thf('26', plain,
% 1.03/1.22      (![X24 : $i, X25 : $i]:
% 1.03/1.22         ((r1_tarski @ X24 @ X25) | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25)))),
% 1.03/1.22      inference('cnf', [status(esa)], [t3_subset])).
% 1.03/1.22  thf('27', plain, ((r1_tarski @ sk_B @ sk_A)),
% 1.03/1.22      inference('sup-', [status(thm)], ['25', '26'])).
% 1.03/1.22  thf(t36_xboole_1, axiom,
% 1.03/1.22    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.03/1.22  thf('28', plain,
% 1.03/1.22      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 1.03/1.22      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.03/1.22  thf(t1_xboole_1, axiom,
% 1.03/1.22    (![A:$i,B:$i,C:$i]:
% 1.03/1.22     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.03/1.22       ( r1_tarski @ A @ C ) ))).
% 1.03/1.22  thf('29', plain,
% 1.03/1.22      (![X1 : $i, X2 : $i, X3 : $i]:
% 1.03/1.22         (~ (r1_tarski @ X1 @ X2)
% 1.03/1.22          | ~ (r1_tarski @ X2 @ X3)
% 1.03/1.22          | (r1_tarski @ X1 @ X3))),
% 1.03/1.22      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.03/1.22  thf('30', plain,
% 1.03/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.22         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 1.03/1.22      inference('sup-', [status(thm)], ['28', '29'])).
% 1.03/1.22  thf('31', plain,
% 1.03/1.22      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)),
% 1.03/1.22      inference('sup-', [status(thm)], ['27', '30'])).
% 1.03/1.22  thf(t79_xboole_1, axiom,
% 1.03/1.22    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 1.03/1.22  thf('32', plain,
% 1.03/1.22      (![X11 : $i, X12 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X12)),
% 1.03/1.22      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.03/1.22  thf(t69_xboole_1, axiom,
% 1.03/1.22    (![A:$i,B:$i]:
% 1.03/1.22     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.03/1.22       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 1.03/1.22  thf('33', plain,
% 1.03/1.22      (![X9 : $i, X10 : $i]:
% 1.03/1.22         (~ (r1_xboole_0 @ X9 @ X10)
% 1.03/1.22          | ~ (r1_tarski @ X9 @ X10)
% 1.03/1.22          | (v1_xboole_0 @ X9))),
% 1.03/1.22      inference('cnf', [status(esa)], [t69_xboole_1])).
% 1.03/1.22  thf('34', plain,
% 1.03/1.22      (![X0 : $i, X1 : $i]:
% 1.03/1.22         ((v1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 1.03/1.22          | ~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 1.03/1.22      inference('sup-', [status(thm)], ['32', '33'])).
% 1.03/1.22  thf('35', plain, ((v1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A))),
% 1.03/1.22      inference('sup-', [status(thm)], ['31', '34'])).
% 1.03/1.22  thf(t48_xboole_1, axiom,
% 1.03/1.22    (![A:$i,B:$i]:
% 1.03/1.22     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.03/1.22  thf('36', plain,
% 1.03/1.22      (![X7 : $i, X8 : $i]:
% 1.03/1.22         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 1.03/1.22           = (k3_xboole_0 @ X7 @ X8))),
% 1.03/1.22      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.03/1.22  thf(l13_xboole_0, axiom,
% 1.03/1.22    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.03/1.22  thf('37', plain,
% 1.03/1.22      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.03/1.22      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.03/1.22  thf(t3_boole, axiom,
% 1.03/1.22    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.03/1.22  thf('38', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 1.03/1.22      inference('cnf', [status(esa)], [t3_boole])).
% 1.03/1.22  thf('39', plain,
% 1.03/1.22      (![X0 : $i, X1 : $i]:
% 1.03/1.22         (((k4_xboole_0 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 1.03/1.22      inference('sup+', [status(thm)], ['37', '38'])).
% 1.03/1.22  thf('40', plain,
% 1.03/1.22      (![X0 : $i, X1 : $i]:
% 1.03/1.22         (((k3_xboole_0 @ X1 @ X0) = (X1))
% 1.03/1.22          | ~ (v1_xboole_0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.03/1.22      inference('sup+', [status(thm)], ['36', '39'])).
% 1.03/1.22  thf('41', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 1.03/1.22      inference('sup-', [status(thm)], ['35', '40'])).
% 1.03/1.22  thf('42', plain, (((sk_B) != (sk_B))),
% 1.03/1.22      inference('demod', [status(thm)], ['6', '24', '41'])).
% 1.03/1.22  thf('43', plain, ($false), inference('simplify', [status(thm)], ['42'])).
% 1.03/1.22  
% 1.03/1.22  % SZS output end Refutation
% 1.03/1.22  
% 1.07/1.23  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
