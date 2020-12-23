%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.w94G83gCLX

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:14 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 132 expanded)
%              Number of leaves         :   27 (  50 expanded)
%              Depth                    :   15
%              Number of atoms          :  555 (1155 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relset_1_type,type,(
    k5_relset_1: $i > $i > $i > $i > $i )).

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

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t33_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( m1_subset_1 @ ( k5_relset_1 @ A @ C @ D @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
       => ( m1_subset_1 @ ( k5_relset_1 @ A @ C @ D @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_relset_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k5_relset_1 @ sk_A @ sk_C @ sk_D @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k5_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k5_relset_1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( ( k5_relset_1 @ X21 @ X22 @ X20 @ X23 )
        = ( k7_relat_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k5_relset_1 @ sk_A @ sk_C @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('7',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc23_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v4_relat_1 @ C @ B ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) )
        & ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ A )
        & ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) @ X7 )
      | ~ ( v4_relat_1 @ X6 @ X8 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc23_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( v4_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('12',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v4_relat_1 @ X4 @ X5 )
      | ( r1_tarski @ ( k1_relat_1 @ X4 ) @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf('17',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) )
      | ~ ( v4_relat_1 @ X6 @ X8 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc23_relat_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('20',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['15','20'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('23',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X4 ) @ X5 )
      | ( v4_relat_1 @ X4 @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v4_relat_1 @ X1 @ ( k2_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12
        = ( k7_relat_1 @ X12 @ X13 ) )
      | ~ ( v4_relat_1 @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( X1
        = ( k7_relat_1 @ X1 @ ( k2_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k7_relat_1 @ X1 @ ( k2_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ sk_D @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_D ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('31',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ sk_D @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12
        = ( k7_relat_1 @ X12 @ X13 ) )
      | ~ ( v4_relat_1 @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( sk_D
        = ( k7_relat_1 @ sk_D @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('35',plain,(
    ! [X0: $i] :
      ( sk_D
      = ( k7_relat_1 @ sk_D @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t107_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ) )).

thf('36',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k7_relat_1 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) )
        = ( k2_xboole_0 @ ( k7_relat_1 @ X9 @ X10 ) @ ( k7_relat_1 @ X9 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t107_relat_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X2 @ X0 ) @ ( k7_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_D )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['35','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_D ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
     => ( ( r1_tarski @ A @ D )
       => ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('45',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( r1_tarski @ X28 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t4_relset_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_D )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('48',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X24 ) @ X25 )
      | ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['21','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['4','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.w94G83gCLX
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:15:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.38/1.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.38/1.57  % Solved by: fo/fo7.sh
% 1.38/1.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.38/1.57  % done 1964 iterations in 1.121s
% 1.38/1.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.38/1.57  % SZS output start Refutation
% 1.38/1.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.38/1.57  thf(k5_relset_1_type, type, k5_relset_1: $i > $i > $i > $i > $i).
% 1.38/1.57  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.38/1.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.38/1.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.38/1.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.38/1.57  thf(sk_B_type, type, sk_B: $i).
% 1.38/1.57  thf(sk_A_type, type, sk_A: $i).
% 1.38/1.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.38/1.57  thf(sk_C_type, type, sk_C: $i).
% 1.38/1.57  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.38/1.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.38/1.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.38/1.57  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.38/1.57  thf(sk_D_type, type, sk_D: $i).
% 1.38/1.57  thf(t33_relset_1, conjecture,
% 1.38/1.57    (![A:$i,B:$i,C:$i,D:$i]:
% 1.38/1.57     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 1.38/1.57       ( m1_subset_1 @
% 1.38/1.57         ( k5_relset_1 @ A @ C @ D @ B ) @ 
% 1.38/1.57         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 1.38/1.57  thf(zf_stmt_0, negated_conjecture,
% 1.38/1.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.38/1.57        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 1.38/1.57          ( m1_subset_1 @
% 1.38/1.57            ( k5_relset_1 @ A @ C @ D @ B ) @ 
% 1.38/1.57            ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )),
% 1.38/1.57    inference('cnf.neg', [status(esa)], [t33_relset_1])).
% 1.38/1.57  thf('0', plain,
% 1.38/1.57      (~ (m1_subset_1 @ (k5_relset_1 @ sk_A @ sk_C @ sk_D @ sk_B) @ 
% 1.38/1.57          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.38/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.57  thf('1', plain,
% 1.38/1.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.38/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.57  thf(redefinition_k5_relset_1, axiom,
% 1.38/1.57    (![A:$i,B:$i,C:$i,D:$i]:
% 1.38/1.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.38/1.57       ( ( k5_relset_1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 1.38/1.57  thf('2', plain,
% 1.38/1.57      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 1.38/1.57         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 1.38/1.57          | ((k5_relset_1 @ X21 @ X22 @ X20 @ X23) = (k7_relat_1 @ X20 @ X23)))),
% 1.38/1.57      inference('cnf', [status(esa)], [redefinition_k5_relset_1])).
% 1.38/1.57  thf('3', plain,
% 1.38/1.57      (![X0 : $i]:
% 1.38/1.57         ((k5_relset_1 @ sk_A @ sk_C @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 1.38/1.57      inference('sup-', [status(thm)], ['1', '2'])).
% 1.38/1.57  thf('4', plain,
% 1.38/1.57      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_B) @ 
% 1.38/1.57          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.38/1.57      inference('demod', [status(thm)], ['0', '3'])).
% 1.38/1.57  thf('5', plain,
% 1.38/1.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.38/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.57  thf(cc2_relset_1, axiom,
% 1.38/1.57    (![A:$i,B:$i,C:$i]:
% 1.38/1.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.38/1.57       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.38/1.57  thf('6', plain,
% 1.38/1.57      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.38/1.57         ((v4_relat_1 @ X17 @ X18)
% 1.38/1.57          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.38/1.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.38/1.57  thf('7', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 1.38/1.57      inference('sup-', [status(thm)], ['5', '6'])).
% 1.38/1.57  thf(fc23_relat_1, axiom,
% 1.38/1.57    (![A:$i,B:$i,C:$i]:
% 1.38/1.57     ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ B ) ) =>
% 1.38/1.57       ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) ) & 
% 1.38/1.57         ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ A ) & 
% 1.38/1.57         ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ))).
% 1.38/1.57  thf('8', plain,
% 1.38/1.57      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.38/1.57         ((v4_relat_1 @ (k7_relat_1 @ X6 @ X7) @ X7)
% 1.38/1.57          | ~ (v4_relat_1 @ X6 @ X8)
% 1.38/1.57          | ~ (v1_relat_1 @ X6))),
% 1.38/1.57      inference('cnf', [status(esa)], [fc23_relat_1])).
% 1.38/1.57  thf('9', plain,
% 1.38/1.57      (![X0 : $i]:
% 1.38/1.57         (~ (v1_relat_1 @ sk_D) | (v4_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X0))),
% 1.38/1.57      inference('sup-', [status(thm)], ['7', '8'])).
% 1.38/1.57  thf('10', plain,
% 1.38/1.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.38/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.57  thf(cc1_relset_1, axiom,
% 1.38/1.57    (![A:$i,B:$i,C:$i]:
% 1.38/1.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.38/1.57       ( v1_relat_1 @ C ) ))).
% 1.38/1.57  thf('11', plain,
% 1.38/1.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.38/1.57         ((v1_relat_1 @ X14)
% 1.38/1.57          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.38/1.57      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.38/1.57  thf('12', plain, ((v1_relat_1 @ sk_D)),
% 1.38/1.57      inference('sup-', [status(thm)], ['10', '11'])).
% 1.38/1.57  thf('13', plain, (![X0 : $i]: (v4_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X0)),
% 1.38/1.57      inference('demod', [status(thm)], ['9', '12'])).
% 1.38/1.57  thf(d18_relat_1, axiom,
% 1.38/1.57    (![A:$i,B:$i]:
% 1.38/1.57     ( ( v1_relat_1 @ B ) =>
% 1.38/1.57       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.38/1.57  thf('14', plain,
% 1.38/1.57      (![X4 : $i, X5 : $i]:
% 1.38/1.57         (~ (v4_relat_1 @ X4 @ X5)
% 1.38/1.57          | (r1_tarski @ (k1_relat_1 @ X4) @ X5)
% 1.38/1.57          | ~ (v1_relat_1 @ X4))),
% 1.38/1.57      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.38/1.57  thf('15', plain,
% 1.38/1.57      (![X0 : $i]:
% 1.38/1.57         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 1.38/1.57          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X0))),
% 1.38/1.57      inference('sup-', [status(thm)], ['13', '14'])).
% 1.38/1.57  thf('16', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 1.38/1.57      inference('sup-', [status(thm)], ['5', '6'])).
% 1.38/1.57  thf('17', plain,
% 1.38/1.57      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.38/1.57         ((v1_relat_1 @ (k7_relat_1 @ X6 @ X7))
% 1.38/1.57          | ~ (v4_relat_1 @ X6 @ X8)
% 1.38/1.57          | ~ (v1_relat_1 @ X6))),
% 1.38/1.57      inference('cnf', [status(esa)], [fc23_relat_1])).
% 1.38/1.57  thf('18', plain,
% 1.38/1.57      (![X0 : $i]:
% 1.38/1.57         (~ (v1_relat_1 @ sk_D) | (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 1.38/1.57      inference('sup-', [status(thm)], ['16', '17'])).
% 1.38/1.57  thf('19', plain, ((v1_relat_1 @ sk_D)),
% 1.38/1.57      inference('sup-', [status(thm)], ['10', '11'])).
% 1.38/1.57  thf('20', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 1.38/1.57      inference('demod', [status(thm)], ['18', '19'])).
% 1.38/1.57  thf('21', plain,
% 1.38/1.57      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X0)),
% 1.38/1.57      inference('demod', [status(thm)], ['15', '20'])).
% 1.38/1.57  thf(t7_xboole_1, axiom,
% 1.38/1.57    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.38/1.57  thf('22', plain,
% 1.38/1.57      (![X2 : $i, X3 : $i]: (r1_tarski @ X2 @ (k2_xboole_0 @ X2 @ X3))),
% 1.38/1.57      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.38/1.57  thf('23', plain,
% 1.38/1.57      (![X4 : $i, X5 : $i]:
% 1.38/1.57         (~ (r1_tarski @ (k1_relat_1 @ X4) @ X5)
% 1.38/1.57          | (v4_relat_1 @ X4 @ X5)
% 1.38/1.57          | ~ (v1_relat_1 @ X4))),
% 1.38/1.57      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.38/1.57  thf('24', plain,
% 1.38/1.57      (![X0 : $i, X1 : $i]:
% 1.38/1.57         (~ (v1_relat_1 @ X1)
% 1.38/1.57          | (v4_relat_1 @ X1 @ (k2_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 1.38/1.57      inference('sup-', [status(thm)], ['22', '23'])).
% 1.38/1.57  thf(t209_relat_1, axiom,
% 1.38/1.57    (![A:$i,B:$i]:
% 1.38/1.57     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.38/1.57       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 1.38/1.57  thf('25', plain,
% 1.38/1.57      (![X12 : $i, X13 : $i]:
% 1.38/1.57         (((X12) = (k7_relat_1 @ X12 @ X13))
% 1.38/1.57          | ~ (v4_relat_1 @ X12 @ X13)
% 1.38/1.57          | ~ (v1_relat_1 @ X12))),
% 1.38/1.57      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.38/1.57  thf('26', plain,
% 1.38/1.57      (![X0 : $i, X1 : $i]:
% 1.38/1.57         (~ (v1_relat_1 @ X1)
% 1.38/1.57          | ~ (v1_relat_1 @ X1)
% 1.38/1.57          | ((X1) = (k7_relat_1 @ X1 @ (k2_xboole_0 @ (k1_relat_1 @ X1) @ X0))))),
% 1.38/1.57      inference('sup-', [status(thm)], ['24', '25'])).
% 1.38/1.57  thf('27', plain,
% 1.38/1.57      (![X0 : $i, X1 : $i]:
% 1.38/1.57         (((X1) = (k7_relat_1 @ X1 @ (k2_xboole_0 @ (k1_relat_1 @ X1) @ X0)))
% 1.38/1.57          | ~ (v1_relat_1 @ X1))),
% 1.38/1.57      inference('simplify', [status(thm)], ['26'])).
% 1.38/1.57  thf('28', plain, (![X0 : $i]: (v4_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X0)),
% 1.38/1.57      inference('demod', [status(thm)], ['9', '12'])).
% 1.38/1.57  thf('29', plain,
% 1.38/1.57      (![X0 : $i]:
% 1.38/1.57         ((v4_relat_1 @ sk_D @ (k2_xboole_0 @ (k1_relat_1 @ sk_D) @ X0))
% 1.38/1.57          | ~ (v1_relat_1 @ sk_D))),
% 1.38/1.57      inference('sup+', [status(thm)], ['27', '28'])).
% 1.38/1.57  thf('30', plain, ((v1_relat_1 @ sk_D)),
% 1.38/1.57      inference('sup-', [status(thm)], ['10', '11'])).
% 1.38/1.57  thf('31', plain,
% 1.38/1.57      (![X0 : $i]:
% 1.38/1.57         (v4_relat_1 @ sk_D @ (k2_xboole_0 @ (k1_relat_1 @ sk_D) @ X0))),
% 1.38/1.57      inference('demod', [status(thm)], ['29', '30'])).
% 1.38/1.57  thf('32', plain,
% 1.38/1.57      (![X12 : $i, X13 : $i]:
% 1.38/1.57         (((X12) = (k7_relat_1 @ X12 @ X13))
% 1.38/1.57          | ~ (v4_relat_1 @ X12 @ X13)
% 1.38/1.57          | ~ (v1_relat_1 @ X12))),
% 1.38/1.57      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.38/1.57  thf('33', plain,
% 1.38/1.57      (![X0 : $i]:
% 1.38/1.57         (~ (v1_relat_1 @ sk_D)
% 1.38/1.57          | ((sk_D)
% 1.38/1.57              = (k7_relat_1 @ sk_D @ (k2_xboole_0 @ (k1_relat_1 @ sk_D) @ X0))))),
% 1.38/1.57      inference('sup-', [status(thm)], ['31', '32'])).
% 1.38/1.57  thf('34', plain, ((v1_relat_1 @ sk_D)),
% 1.38/1.57      inference('sup-', [status(thm)], ['10', '11'])).
% 1.38/1.57  thf('35', plain,
% 1.38/1.57      (![X0 : $i]:
% 1.38/1.57         ((sk_D)
% 1.38/1.57           = (k7_relat_1 @ sk_D @ (k2_xboole_0 @ (k1_relat_1 @ sk_D) @ X0)))),
% 1.38/1.57      inference('demod', [status(thm)], ['33', '34'])).
% 1.38/1.57  thf(t107_relat_1, axiom,
% 1.38/1.57    (![A:$i,B:$i,C:$i]:
% 1.38/1.57     ( ( v1_relat_1 @ C ) =>
% 1.38/1.57       ( ( k7_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 1.38/1.57         ( k2_xboole_0 @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ))).
% 1.38/1.57  thf('36', plain,
% 1.38/1.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.38/1.57         (((k7_relat_1 @ X9 @ (k2_xboole_0 @ X10 @ X11))
% 1.38/1.57            = (k2_xboole_0 @ (k7_relat_1 @ X9 @ X10) @ (k7_relat_1 @ X9 @ X11)))
% 1.38/1.57          | ~ (v1_relat_1 @ X9))),
% 1.38/1.57      inference('cnf', [status(esa)], [t107_relat_1])).
% 1.38/1.57  thf(commutativity_k2_xboole_0, axiom,
% 1.38/1.57    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.38/1.57  thf('37', plain,
% 1.38/1.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.38/1.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.38/1.57  thf('38', plain,
% 1.38/1.57      (![X2 : $i, X3 : $i]: (r1_tarski @ X2 @ (k2_xboole_0 @ X2 @ X3))),
% 1.38/1.57      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.38/1.57  thf('39', plain,
% 1.38/1.57      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.38/1.57      inference('sup+', [status(thm)], ['37', '38'])).
% 1.38/1.57  thf('40', plain,
% 1.38/1.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.57         ((r1_tarski @ (k7_relat_1 @ X2 @ X0) @ 
% 1.38/1.57           (k7_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 1.38/1.57          | ~ (v1_relat_1 @ X2))),
% 1.38/1.57      inference('sup+', [status(thm)], ['36', '39'])).
% 1.38/1.57  thf('41', plain,
% 1.38/1.57      (![X0 : $i]:
% 1.38/1.57         ((r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ sk_D) | ~ (v1_relat_1 @ sk_D))),
% 1.38/1.57      inference('sup+', [status(thm)], ['35', '40'])).
% 1.38/1.57  thf('42', plain, ((v1_relat_1 @ sk_D)),
% 1.38/1.57      inference('sup-', [status(thm)], ['10', '11'])).
% 1.38/1.57  thf('43', plain, (![X0 : $i]: (r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ sk_D)),
% 1.38/1.57      inference('demod', [status(thm)], ['41', '42'])).
% 1.38/1.57  thf('44', plain,
% 1.38/1.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.38/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.57  thf(t4_relset_1, axiom,
% 1.38/1.57    (![A:$i,B:$i,C:$i,D:$i]:
% 1.38/1.57     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 1.38/1.57       ( ( r1_tarski @ A @ D ) =>
% 1.38/1.57         ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 1.38/1.57  thf('45', plain,
% 1.38/1.57      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.38/1.57         ((m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 1.38/1.57          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 1.38/1.57          | ~ (r1_tarski @ X28 @ X31))),
% 1.38/1.57      inference('cnf', [status(esa)], [t4_relset_1])).
% 1.38/1.57  thf('46', plain,
% 1.38/1.57      (![X0 : $i]:
% 1.38/1.57         (~ (r1_tarski @ X0 @ sk_D)
% 1.38/1.57          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 1.38/1.57      inference('sup-', [status(thm)], ['44', '45'])).
% 1.38/1.57  thf('47', plain,
% 1.38/1.57      (![X0 : $i]:
% 1.38/1.57         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 1.38/1.57          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.38/1.57      inference('sup-', [status(thm)], ['43', '46'])).
% 1.38/1.57  thf(t13_relset_1, axiom,
% 1.38/1.57    (![A:$i,B:$i,C:$i,D:$i]:
% 1.38/1.57     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 1.38/1.57       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 1.38/1.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 1.38/1.57  thf('48', plain,
% 1.38/1.57      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.38/1.57         (~ (r1_tarski @ (k1_relat_1 @ X24) @ X25)
% 1.38/1.57          | (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.38/1.57          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 1.38/1.57      inference('cnf', [status(esa)], [t13_relset_1])).
% 1.38/1.57  thf('49', plain,
% 1.38/1.57      (![X0 : $i, X1 : $i]:
% 1.38/1.57         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 1.38/1.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 1.38/1.57          | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X1))),
% 1.38/1.57      inference('sup-', [status(thm)], ['47', '48'])).
% 1.38/1.57  thf('50', plain,
% 1.38/1.57      (![X0 : $i]:
% 1.38/1.57         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 1.38/1.57          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_C)))),
% 1.38/1.57      inference('sup-', [status(thm)], ['21', '49'])).
% 1.38/1.57  thf('51', plain, ($false), inference('demod', [status(thm)], ['4', '50'])).
% 1.38/1.57  
% 1.38/1.57  % SZS output end Refutation
% 1.38/1.57  
% 1.38/1.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
