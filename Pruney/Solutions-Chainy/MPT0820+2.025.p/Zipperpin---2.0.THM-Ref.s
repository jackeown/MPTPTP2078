%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.li0Opx09JU

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:51 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 128 expanded)
%              Number of leaves         :   32 (  53 expanded)
%              Depth                    :   14
%              Number of atoms          :  476 ( 870 expanded)
%              Number of equality atoms :   20 (  42 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

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

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X8 @ X9 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X8 @ X9 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X15: $i] :
      ( ( ( k3_relat_1 @ X15 )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X15 ) @ ( k1_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X25 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('11',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('16',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['13','16'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('22',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('23',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X18
        = ( k7_relat_1 @ X18 @ X19 ) )
      | ~ ( v4_relat_1 @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('29',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['25','30'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('32',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('33',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf('35',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('38',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X5 @ X4 )
      | ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ X1 ) @ ( k2_xboole_0 @ X0 @ sk_A ) )
      | ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) @ ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('43',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['7','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf('46',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['0','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.li0Opx09JU
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:01:47 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.54/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.71  % Solved by: fo/fo7.sh
% 0.54/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.71  % done 590 iterations in 0.247s
% 0.54/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.71  % SZS output start Refutation
% 0.54/0.71  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.54/0.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.54/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.54/0.71  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.54/0.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.54/0.71  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.54/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.54/0.71  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.54/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.71  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.54/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.71  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.71  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.54/0.71  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.54/0.71  thf(t19_relset_1, conjecture,
% 0.54/0.71    (![A:$i,B:$i,C:$i]:
% 0.54/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.71       ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.54/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.71    (~( ![A:$i,B:$i,C:$i]:
% 0.54/0.71        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.71          ( r1_tarski @ ( k3_relat_1 @ C ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 0.54/0.71    inference('cnf.neg', [status(esa)], [t19_relset_1])).
% 0.54/0.71  thf('0', plain,
% 0.54/0.71      (~ (r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf(d6_relat_1, axiom,
% 0.54/0.71    (![A:$i]:
% 0.54/0.71     ( ( v1_relat_1 @ A ) =>
% 0.54/0.71       ( ( k3_relat_1 @ A ) =
% 0.54/0.71         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.54/0.71  thf('1', plain,
% 0.54/0.71      (![X15 : $i]:
% 0.54/0.71         (((k3_relat_1 @ X15)
% 0.54/0.71            = (k2_xboole_0 @ (k1_relat_1 @ X15) @ (k2_relat_1 @ X15)))
% 0.54/0.71          | ~ (v1_relat_1 @ X15))),
% 0.54/0.71      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.54/0.71  thf(commutativity_k2_tarski, axiom,
% 0.54/0.71    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.54/0.71  thf('2', plain,
% 0.54/0.71      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 0.54/0.71      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.54/0.71  thf(l51_zfmisc_1, axiom,
% 0.54/0.71    (![A:$i,B:$i]:
% 0.54/0.71     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.54/0.71  thf('3', plain,
% 0.54/0.71      (![X8 : $i, X9 : $i]:
% 0.54/0.71         ((k3_tarski @ (k2_tarski @ X8 @ X9)) = (k2_xboole_0 @ X8 @ X9))),
% 0.54/0.71      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.54/0.71  thf('4', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.54/0.71      inference('sup+', [status(thm)], ['2', '3'])).
% 0.54/0.71  thf('5', plain,
% 0.54/0.71      (![X8 : $i, X9 : $i]:
% 0.54/0.71         ((k3_tarski @ (k2_tarski @ X8 @ X9)) = (k2_xboole_0 @ X8 @ X9))),
% 0.54/0.71      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.54/0.71  thf('6', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.54/0.71      inference('sup+', [status(thm)], ['4', '5'])).
% 0.54/0.71  thf('7', plain,
% 0.54/0.71      (![X15 : $i]:
% 0.54/0.71         (((k3_relat_1 @ X15)
% 0.54/0.71            = (k2_xboole_0 @ (k2_relat_1 @ X15) @ (k1_relat_1 @ X15)))
% 0.54/0.71          | ~ (v1_relat_1 @ X15))),
% 0.54/0.71      inference('demod', [status(thm)], ['1', '6'])).
% 0.54/0.71  thf('8', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.54/0.71      inference('sup+', [status(thm)], ['4', '5'])).
% 0.54/0.71  thf('9', plain,
% 0.54/0.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf(dt_k2_relset_1, axiom,
% 0.54/0.71    (![A:$i,B:$i,C:$i]:
% 0.54/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.71       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.54/0.71  thf('10', plain,
% 0.54/0.71      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.54/0.71         ((m1_subset_1 @ (k2_relset_1 @ X25 @ X26 @ X27) @ (k1_zfmisc_1 @ X26))
% 0.54/0.71          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.54/0.71      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.54/0.71  thf('11', plain,
% 0.54/0.71      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 0.54/0.71      inference('sup-', [status(thm)], ['9', '10'])).
% 0.54/0.71  thf(t3_subset, axiom,
% 0.54/0.71    (![A:$i,B:$i]:
% 0.54/0.71     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.54/0.71  thf('12', plain,
% 0.54/0.71      (![X10 : $i, X11 : $i]:
% 0.54/0.71         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.54/0.71      inference('cnf', [status(esa)], [t3_subset])).
% 0.54/0.71  thf('13', plain, ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_C) @ sk_B)),
% 0.54/0.71      inference('sup-', [status(thm)], ['11', '12'])).
% 0.54/0.71  thf('14', plain,
% 0.54/0.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf(redefinition_k2_relset_1, axiom,
% 0.54/0.71    (![A:$i,B:$i,C:$i]:
% 0.54/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.71       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.54/0.71  thf('15', plain,
% 0.54/0.71      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.54/0.71         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 0.54/0.71          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.54/0.71      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.54/0.71  thf('16', plain,
% 0.54/0.71      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.54/0.71      inference('sup-', [status(thm)], ['14', '15'])).
% 0.54/0.71  thf('17', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.54/0.71      inference('demod', [status(thm)], ['13', '16'])).
% 0.54/0.71  thf(t10_xboole_1, axiom,
% 0.54/0.71    (![A:$i,B:$i,C:$i]:
% 0.54/0.71     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.54/0.71  thf('18', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.71         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ X1)))),
% 0.54/0.71      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.54/0.71  thf('19', plain,
% 0.54/0.71      (![X0 : $i]:
% 0.54/0.71         (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_B))),
% 0.54/0.71      inference('sup-', [status(thm)], ['17', '18'])).
% 0.54/0.71  thf('20', plain,
% 0.54/0.71      (![X0 : $i]:
% 0.54/0.71         (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_B @ X0))),
% 0.54/0.71      inference('sup+', [status(thm)], ['8', '19'])).
% 0.54/0.71  thf('21', plain,
% 0.54/0.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf(cc2_relset_1, axiom,
% 0.54/0.71    (![A:$i,B:$i,C:$i]:
% 0.54/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.71       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.54/0.71  thf('22', plain,
% 0.54/0.71      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.54/0.71         ((v4_relat_1 @ X22 @ X23)
% 0.54/0.71          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.54/0.71      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.54/0.71  thf('23', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.54/0.71      inference('sup-', [status(thm)], ['21', '22'])).
% 0.54/0.71  thf(t209_relat_1, axiom,
% 0.54/0.71    (![A:$i,B:$i]:
% 0.54/0.71     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.54/0.71       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.54/0.71  thf('24', plain,
% 0.54/0.71      (![X18 : $i, X19 : $i]:
% 0.54/0.71         (((X18) = (k7_relat_1 @ X18 @ X19))
% 0.54/0.71          | ~ (v4_relat_1 @ X18 @ X19)
% 0.54/0.71          | ~ (v1_relat_1 @ X18))),
% 0.54/0.71      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.54/0.71  thf('25', plain,
% 0.54/0.71      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.54/0.71      inference('sup-', [status(thm)], ['23', '24'])).
% 0.54/0.71  thf('26', plain,
% 0.54/0.71      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf(cc2_relat_1, axiom,
% 0.54/0.71    (![A:$i]:
% 0.54/0.71     ( ( v1_relat_1 @ A ) =>
% 0.54/0.71       ( ![B:$i]:
% 0.54/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.54/0.71  thf('27', plain,
% 0.54/0.71      (![X13 : $i, X14 : $i]:
% 0.54/0.71         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.54/0.71          | (v1_relat_1 @ X13)
% 0.54/0.71          | ~ (v1_relat_1 @ X14))),
% 0.54/0.71      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.54/0.71  thf('28', plain,
% 0.54/0.71      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.54/0.71      inference('sup-', [status(thm)], ['26', '27'])).
% 0.54/0.71  thf(fc6_relat_1, axiom,
% 0.54/0.71    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.54/0.71  thf('29', plain,
% 0.54/0.71      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 0.54/0.71      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.54/0.71  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.71      inference('demod', [status(thm)], ['28', '29'])).
% 0.54/0.71  thf('31', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.54/0.71      inference('demod', [status(thm)], ['25', '30'])).
% 0.54/0.71  thf(t87_relat_1, axiom,
% 0.54/0.71    (![A:$i,B:$i]:
% 0.54/0.71     ( ( v1_relat_1 @ B ) =>
% 0.54/0.71       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.54/0.71  thf('32', plain,
% 0.54/0.71      (![X20 : $i, X21 : $i]:
% 0.54/0.71         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X20 @ X21)) @ X21)
% 0.54/0.71          | ~ (v1_relat_1 @ X20))),
% 0.54/0.71      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.54/0.71  thf('33', plain,
% 0.54/0.71      (((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A) | ~ (v1_relat_1 @ sk_C))),
% 0.54/0.71      inference('sup+', [status(thm)], ['31', '32'])).
% 0.54/0.71  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.71      inference('demod', [status(thm)], ['28', '29'])).
% 0.54/0.71  thf('35', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.54/0.71      inference('demod', [status(thm)], ['33', '34'])).
% 0.54/0.71  thf('36', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.71         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ X1)))),
% 0.54/0.71      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.54/0.71  thf('37', plain,
% 0.54/0.71      (![X0 : $i]:
% 0.54/0.71         (r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_xboole_0 @ X0 @ sk_A))),
% 0.54/0.71      inference('sup-', [status(thm)], ['35', '36'])).
% 0.54/0.71  thf(t8_xboole_1, axiom,
% 0.54/0.71    (![A:$i,B:$i,C:$i]:
% 0.54/0.71     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.54/0.71       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.54/0.71  thf('38', plain,
% 0.54/0.71      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.54/0.71         (~ (r1_tarski @ X3 @ X4)
% 0.54/0.71          | ~ (r1_tarski @ X5 @ X4)
% 0.54/0.71          | (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.54/0.71      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.54/0.71  thf('39', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ X1) @ 
% 0.54/0.71           (k2_xboole_0 @ X0 @ sk_A))
% 0.54/0.71          | ~ (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ sk_A)))),
% 0.54/0.71      inference('sup-', [status(thm)], ['37', '38'])).
% 0.54/0.71  thf('40', plain,
% 0.54/0.71      ((r1_tarski @ 
% 0.54/0.71        (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)) @ 
% 0.54/0.71        (k2_xboole_0 @ sk_B @ sk_A))),
% 0.54/0.71      inference('sup-', [status(thm)], ['20', '39'])).
% 0.54/0.71  thf('41', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.54/0.71      inference('sup+', [status(thm)], ['4', '5'])).
% 0.54/0.71  thf('42', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.54/0.71      inference('sup+', [status(thm)], ['4', '5'])).
% 0.54/0.71  thf('43', plain,
% 0.54/0.71      ((r1_tarski @ 
% 0.54/0.71        (k2_xboole_0 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C)) @ 
% 0.54/0.71        (k2_xboole_0 @ sk_A @ sk_B))),
% 0.54/0.71      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.54/0.71  thf('44', plain,
% 0.54/0.71      (((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))
% 0.54/0.71        | ~ (v1_relat_1 @ sk_C))),
% 0.54/0.71      inference('sup+', [status(thm)], ['7', '43'])).
% 0.54/0.71  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.71      inference('demod', [status(thm)], ['28', '29'])).
% 0.54/0.71  thf('46', plain,
% 0.54/0.71      ((r1_tarski @ (k3_relat_1 @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_B))),
% 0.54/0.71      inference('demod', [status(thm)], ['44', '45'])).
% 0.54/0.71  thf('47', plain, ($false), inference('demod', [status(thm)], ['0', '46'])).
% 0.54/0.71  
% 0.54/0.71  % SZS output end Refutation
% 0.54/0.71  
% 0.54/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
