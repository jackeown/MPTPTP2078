%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uu53dz3y9j

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:52 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 102 expanded)
%              Number of leaves         :   29 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  445 ( 690 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(t19_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
       => ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t19_relset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X15: $i] :
      ( ( ( k3_relat_1 @ X15 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X15 ) @ ( k2_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('3',plain,(
    ! [X15: $i] :
      ( ( ( k3_relat_1 @ X15 )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X15 ) @ ( k1_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X25 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('7',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('9',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('12',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['9','12'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ X4 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('19',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X18
        = ( k7_relat_1 @ X18 @ X19 ) )
      | ~ ( v4_relat_1 @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('23',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('25',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['21','26'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('28',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('29',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ X4 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_xboole_0 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_xboole_0 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('34',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X7 @ X6 )
      | ( r1_tarski @ ( k2_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ X1 ) @ ( k2_xboole_0 @ X0 @ sk_A ) )
      | ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) @ ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['16','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('39',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['3','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('42',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['0','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uu53dz3y9j
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:46:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.52/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.73  % Solved by: fo/fo7.sh
% 0.52/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.73  % done 576 iterations in 0.281s
% 0.52/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.73  % SZS output start Refutation
% 0.52/0.73  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.52/0.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.52/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.52/0.73  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.52/0.73  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.52/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.73  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.52/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.73  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.52/0.73  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.52/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.73  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.52/0.73  thf(t19_relset_1, conjecture,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.73       ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.52/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.73    (~( ![A:$i,B:$i,C:$i]:
% 0.52/0.73        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.73          ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 0.52/0.73    inference('cnf.neg', [status(esa)], [t19_relset_1])).
% 0.52/0.73  thf('0', plain,
% 0.52/0.73      (~ (r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(d6_relat_1, axiom,
% 0.52/0.73    (![A:$i]:
% 0.52/0.73     ( ( v1_relat_1 @ A ) =>
% 0.52/0.73       ( ( k3_relat_1 @ A ) =
% 0.52/0.73         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.52/0.73  thf('1', plain,
% 0.52/0.73      (![X15 : $i]:
% 0.52/0.73         (((k3_relat_1 @ X15)
% 0.52/0.73            = (k2_xboole_0 @ (k1_relat_1 @ X15) @ (k2_relat_1 @ X15)))
% 0.52/0.73          | ~ (v1_relat_1 @ X15))),
% 0.52/0.73      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.52/0.73  thf(commutativity_k2_xboole_0, axiom,
% 0.52/0.73    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.52/0.73  thf('2', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.52/0.73  thf('3', plain,
% 0.52/0.73      (![X15 : $i]:
% 0.52/0.73         (((k3_relat_1 @ X15)
% 0.52/0.73            = (k2_xboole_0 @ (k2_relat_1 @ X15) @ (k1_relat_1 @ X15)))
% 0.52/0.73          | ~ (v1_relat_1 @ X15))),
% 0.52/0.73      inference('demod', [status(thm)], ['1', '2'])).
% 0.52/0.73  thf('4', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.52/0.73  thf('5', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(dt_k2_relset_1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.73       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.52/0.73  thf('6', plain,
% 0.52/0.73      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.52/0.73         ((m1_subset_1 @ (k2_relset_1 @ X25 @ X26 @ X27) @ (k1_zfmisc_1 @ X26))
% 0.52/0.73          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.52/0.73      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.52/0.73  thf('7', plain,
% 0.52/0.73      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 0.52/0.73      inference('sup-', [status(thm)], ['5', '6'])).
% 0.52/0.73  thf(t3_subset, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.52/0.73  thf('8', plain,
% 0.52/0.73      (![X10 : $i, X11 : $i]:
% 0.52/0.73         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t3_subset])).
% 0.52/0.73  thf('9', plain, ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_C) @ sk_B)),
% 0.52/0.73      inference('sup-', [status(thm)], ['7', '8'])).
% 0.52/0.73  thf('10', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(redefinition_k2_relset_1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.73       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.52/0.73  thf('11', plain,
% 0.52/0.73      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.52/0.73         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 0.52/0.73          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.52/0.73      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.52/0.73  thf('12', plain,
% 0.52/0.73      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.52/0.73      inference('sup-', [status(thm)], ['10', '11'])).
% 0.52/0.73  thf('13', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.52/0.73      inference('demod', [status(thm)], ['9', '12'])).
% 0.52/0.73  thf(t10_xboole_1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.52/0.73  thf('14', plain,
% 0.52/0.73      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.52/0.73         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ X2 @ (k2_xboole_0 @ X4 @ X3)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.52/0.73  thf('15', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_B))),
% 0.52/0.73      inference('sup-', [status(thm)], ['13', '14'])).
% 0.52/0.73  thf('16', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_B @ X0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['4', '15'])).
% 0.52/0.73  thf('17', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(cc2_relset_1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.73       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.52/0.73  thf('18', plain,
% 0.52/0.73      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.52/0.73         ((v4_relat_1 @ X22 @ X23)
% 0.52/0.73          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.52/0.73      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.52/0.73  thf('19', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.52/0.73      inference('sup-', [status(thm)], ['17', '18'])).
% 0.52/0.73  thf(t209_relat_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.52/0.73       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.52/0.73  thf('20', plain,
% 0.52/0.73      (![X18 : $i, X19 : $i]:
% 0.52/0.73         (((X18) = (k7_relat_1 @ X18 @ X19))
% 0.52/0.73          | ~ (v4_relat_1 @ X18 @ X19)
% 0.52/0.73          | ~ (v1_relat_1 @ X18))),
% 0.52/0.73      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.52/0.73  thf('21', plain,
% 0.52/0.73      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['19', '20'])).
% 0.52/0.73  thf('22', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(cc2_relat_1, axiom,
% 0.52/0.73    (![A:$i]:
% 0.52/0.73     ( ( v1_relat_1 @ A ) =>
% 0.52/0.73       ( ![B:$i]:
% 0.52/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.52/0.73  thf('23', plain,
% 0.52/0.73      (![X13 : $i, X14 : $i]:
% 0.52/0.73         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.52/0.73          | (v1_relat_1 @ X13)
% 0.52/0.73          | ~ (v1_relat_1 @ X14))),
% 0.52/0.73      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.52/0.73  thf('24', plain,
% 0.52/0.73      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.52/0.73      inference('sup-', [status(thm)], ['22', '23'])).
% 0.52/0.73  thf(fc6_relat_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.52/0.73  thf('25', plain,
% 0.52/0.73      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 0.52/0.73      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.52/0.73  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.73      inference('demod', [status(thm)], ['24', '25'])).
% 0.52/0.73  thf('27', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.52/0.73      inference('demod', [status(thm)], ['21', '26'])).
% 0.52/0.73  thf(t87_relat_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( v1_relat_1 @ B ) =>
% 0.52/0.73       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.52/0.73  thf('28', plain,
% 0.52/0.73      (![X20 : $i, X21 : $i]:
% 0.52/0.73         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X20 @ X21)) @ X21)
% 0.52/0.73          | ~ (v1_relat_1 @ X20))),
% 0.52/0.73      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.52/0.73  thf('29', plain,
% 0.52/0.73      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.52/0.73         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ X2 @ (k2_xboole_0 @ X4 @ X3)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.52/0.73  thf('30', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.73         (~ (v1_relat_1 @ X1)
% 0.52/0.73          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.52/0.73             (k2_xboole_0 @ X2 @ X0)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['28', '29'])).
% 0.52/0.73  thf('31', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_A))
% 0.52/0.73          | ~ (v1_relat_1 @ sk_C))),
% 0.52/0.73      inference('sup+', [status(thm)], ['27', '30'])).
% 0.52/0.73  thf('32', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.73      inference('demod', [status(thm)], ['24', '25'])).
% 0.52/0.73  thf('33', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         (r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_A))),
% 0.52/0.73      inference('demod', [status(thm)], ['31', '32'])).
% 0.52/0.73  thf(t8_xboole_1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.52/0.73       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.52/0.73  thf('34', plain,
% 0.52/0.73      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.52/0.73         (~ (r1_tarski @ X5 @ X6)
% 0.52/0.73          | ~ (r1_tarski @ X7 @ X6)
% 0.52/0.73          | (r1_tarski @ (k2_xboole_0 @ X5 @ X7) @ X6))),
% 0.52/0.73      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.52/0.73  thf('35', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ X1) @ 
% 0.52/0.73           (k2_xboole_0 @ X0 @ sk_A))
% 0.52/0.73          | ~ (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ sk_A)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['33', '34'])).
% 0.52/0.73  thf('36', plain,
% 0.52/0.73      ((r1_tarski @ 
% 0.52/0.73        (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)) @ 
% 0.52/0.73        (k2_xboole_0 @ sk_B @ sk_A))),
% 0.52/0.73      inference('sup-', [status(thm)], ['16', '35'])).
% 0.52/0.73  thf('37', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.52/0.73  thf('38', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.52/0.73  thf('39', plain,
% 0.52/0.73      ((r1_tarski @ 
% 0.52/0.73        (k2_xboole_0 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C)) @ 
% 0.52/0.73        (k2_xboole_0 @ sk_A @ sk_B))),
% 0.52/0.73      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.52/0.73  thf('40', plain,
% 0.52/0.73      (((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))
% 0.52/0.73        | ~ (v1_relat_1 @ sk_C))),
% 0.52/0.73      inference('sup+', [status(thm)], ['3', '39'])).
% 0.52/0.73  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.73      inference('demod', [status(thm)], ['24', '25'])).
% 0.52/0.73  thf('42', plain,
% 0.52/0.73      ((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 0.52/0.73      inference('demod', [status(thm)], ['40', '41'])).
% 0.52/0.73  thf('43', plain, ($false), inference('demod', [status(thm)], ['0', '42'])).
% 0.52/0.73  
% 0.52/0.73  % SZS output end Refutation
% 0.52/0.73  
% 0.52/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
