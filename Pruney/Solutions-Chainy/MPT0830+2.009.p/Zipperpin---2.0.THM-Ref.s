%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4iVZ5kdR1v

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:14 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 164 expanded)
%              Number of leaves         :   26 (  60 expanded)
%              Depth                    :   16
%              Number of atoms          :  589 (1434 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k5_relset_1_type,type,(
    k5_relset_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('7',plain,(
    v5_relat_1 @ sk_D @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ) ),
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
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['9','12'])).

thf(t99_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k2_relat_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) ) @ ( k2_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t99_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_C )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('23',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['21','22'])).

thf(fc23_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v4_relat_1 @ C @ B ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) )
        & ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ A )
        & ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ) )).

thf('24',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v4_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) @ X10 )
      | ~ ( v4_relat_1 @ X9 @ X11 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc23_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( v4_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('27',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('28',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('33',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X24 ) @ X25 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X24 ) @ X26 )
      | ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('37',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('38',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['21','22'])).

thf('39',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v4_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) @ X11 )
      | ~ ( v4_relat_1 @ X9 @ X11 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc23_relat_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( v4_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('42',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X24 ) @ X25 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X24 ) @ X26 )
      | ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['35','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('53',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['34','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['19','56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['4','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4iVZ5kdR1v
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:06:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.62  % Solved by: fo/fo7.sh
% 0.45/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.62  % done 228 iterations in 0.173s
% 0.45/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.62  % SZS output start Refutation
% 0.45/0.62  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.45/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.62  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.45/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.62  thf(sk_D_type, type, sk_D: $i).
% 0.45/0.62  thf(k5_relset_1_type, type, k5_relset_1: $i > $i > $i > $i > $i).
% 0.45/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.62  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.45/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.62  thf(t33_relset_1, conjecture,
% 0.45/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.62     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.45/0.62       ( m1_subset_1 @
% 0.45/0.62         ( k5_relset_1 @ A @ C @ D @ B ) @ 
% 0.45/0.62         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.45/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.62    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.62        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.45/0.62          ( m1_subset_1 @
% 0.45/0.62            ( k5_relset_1 @ A @ C @ D @ B ) @ 
% 0.45/0.62            ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )),
% 0.45/0.62    inference('cnf.neg', [status(esa)], [t33_relset_1])).
% 0.45/0.62  thf('0', plain,
% 0.45/0.62      (~ (m1_subset_1 @ (k5_relset_1 @ sk_A @ sk_C @ sk_D @ sk_B) @ 
% 0.45/0.62          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.62  thf('1', plain,
% 0.45/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.62  thf(redefinition_k5_relset_1, axiom,
% 0.45/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.62       ( ( k5_relset_1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.45/0.62  thf('2', plain,
% 0.45/0.62      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.62         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.45/0.62          | ((k5_relset_1 @ X21 @ X22 @ X20 @ X23) = (k7_relat_1 @ X20 @ X23)))),
% 0.45/0.62      inference('cnf', [status(esa)], [redefinition_k5_relset_1])).
% 0.45/0.62  thf('3', plain,
% 0.45/0.62      (![X0 : $i]:
% 0.45/0.62         ((k5_relset_1 @ sk_A @ sk_C @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.45/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.62  thf('4', plain,
% 0.45/0.62      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_B) @ 
% 0.45/0.62          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.45/0.62      inference('demod', [status(thm)], ['0', '3'])).
% 0.45/0.62  thf('5', plain,
% 0.45/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.62  thf(cc2_relset_1, axiom,
% 0.45/0.62    (![A:$i,B:$i,C:$i]:
% 0.45/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.62       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.45/0.63  thf('6', plain,
% 0.45/0.63      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.63         ((v5_relat_1 @ X17 @ X19)
% 0.45/0.63          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.45/0.63      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.63  thf('7', plain, ((v5_relat_1 @ sk_D @ sk_C)),
% 0.45/0.63      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.63  thf(d19_relat_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( v1_relat_1 @ B ) =>
% 0.45/0.63       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.45/0.63  thf('8', plain,
% 0.45/0.63      (![X5 : $i, X6 : $i]:
% 0.45/0.63         (~ (v5_relat_1 @ X5 @ X6)
% 0.45/0.63          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.45/0.63          | ~ (v1_relat_1 @ X5))),
% 0.45/0.63      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.45/0.63  thf('9', plain,
% 0.45/0.63      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C))),
% 0.45/0.63      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.63  thf('10', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(cc1_relset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.63       ( v1_relat_1 @ C ) ))).
% 0.45/0.63  thf('11', plain,
% 0.45/0.63      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.45/0.63         ((v1_relat_1 @ X14)
% 0.45/0.63          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.45/0.63      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.63  thf('12', plain, ((v1_relat_1 @ sk_D)),
% 0.45/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.63  thf('13', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.45/0.63      inference('demod', [status(thm)], ['9', '12'])).
% 0.45/0.63  thf(t99_relat_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( v1_relat_1 @ B ) =>
% 0.45/0.63       ( r1_tarski @
% 0.45/0.63         ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k2_relat_1 @ B ) ) ))).
% 0.45/0.63  thf('14', plain,
% 0.45/0.63      (![X12 : $i, X13 : $i]:
% 0.45/0.63         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) @ 
% 0.45/0.63           (k2_relat_1 @ X12))
% 0.45/0.63          | ~ (v1_relat_1 @ X12))),
% 0.45/0.63      inference('cnf', [status(esa)], [t99_relat_1])).
% 0.45/0.63  thf(t1_xboole_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.45/0.63       ( r1_tarski @ A @ C ) ))).
% 0.45/0.63  thf('15', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         (~ (r1_tarski @ X0 @ X1)
% 0.45/0.63          | ~ (r1_tarski @ X1 @ X2)
% 0.45/0.63          | (r1_tarski @ X0 @ X2))),
% 0.45/0.63      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.45/0.63  thf('16', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ X0)
% 0.45/0.63          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ X2)
% 0.45/0.63          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X2))),
% 0.45/0.63      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.63  thf('17', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_C)
% 0.45/0.63          | ~ (v1_relat_1 @ sk_D))),
% 0.45/0.63      inference('sup-', [status(thm)], ['13', '16'])).
% 0.45/0.63  thf('18', plain, ((v1_relat_1 @ sk_D)),
% 0.45/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.63  thf('19', plain,
% 0.45/0.63      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_C)),
% 0.45/0.63      inference('demod', [status(thm)], ['17', '18'])).
% 0.45/0.63  thf(dt_k7_relat_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.45/0.63  thf('20', plain,
% 0.45/0.63      (![X7 : $i, X8 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k7_relat_1 @ X7 @ X8)))),
% 0.45/0.63      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.45/0.63  thf('21', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('22', plain,
% 0.45/0.63      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.63         ((v4_relat_1 @ X17 @ X18)
% 0.45/0.63          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.45/0.63      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.63  thf('23', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 0.45/0.63      inference('sup-', [status(thm)], ['21', '22'])).
% 0.45/0.63  thf(fc23_relat_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ B ) ) =>
% 0.45/0.63       ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) ) & 
% 0.45/0.63         ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ A ) & 
% 0.45/0.63         ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ))).
% 0.45/0.63  thf('24', plain,
% 0.45/0.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.63         ((v4_relat_1 @ (k7_relat_1 @ X9 @ X10) @ X10)
% 0.45/0.63          | ~ (v4_relat_1 @ X9 @ X11)
% 0.45/0.63          | ~ (v1_relat_1 @ X9))),
% 0.45/0.63      inference('cnf', [status(esa)], [fc23_relat_1])).
% 0.45/0.63  thf('25', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ sk_D) | (v4_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['23', '24'])).
% 0.45/0.63  thf('26', plain, ((v1_relat_1 @ sk_D)),
% 0.45/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.63  thf('27', plain, (![X0 : $i]: (v4_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X0)),
% 0.45/0.63      inference('demod', [status(thm)], ['25', '26'])).
% 0.45/0.63  thf(d18_relat_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( v1_relat_1 @ B ) =>
% 0.45/0.63       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.45/0.63  thf('28', plain,
% 0.45/0.63      (![X3 : $i, X4 : $i]:
% 0.45/0.63         (~ (v4_relat_1 @ X3 @ X4)
% 0.45/0.63          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 0.45/0.63          | ~ (v1_relat_1 @ X3))),
% 0.45/0.63      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.45/0.63  thf('29', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 0.45/0.63          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['27', '28'])).
% 0.45/0.63  thf('30', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ sk_D)
% 0.45/0.63          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['20', '29'])).
% 0.45/0.63  thf('31', plain, ((v1_relat_1 @ sk_D)),
% 0.45/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.63  thf('32', plain,
% 0.45/0.63      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X0)),
% 0.45/0.63      inference('demod', [status(thm)], ['30', '31'])).
% 0.45/0.63  thf(t11_relset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( v1_relat_1 @ C ) =>
% 0.45/0.63       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.45/0.63           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.45/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.45/0.63  thf('33', plain,
% 0.45/0.63      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.45/0.63         (~ (r1_tarski @ (k1_relat_1 @ X24) @ X25)
% 0.45/0.63          | ~ (r1_tarski @ (k2_relat_1 @ X24) @ X26)
% 0.45/0.63          | (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.45/0.63          | ~ (v1_relat_1 @ X24))),
% 0.45/0.63      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.45/0.63  thf('34', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 0.45/0.63          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.45/0.63             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.45/0.63          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['32', '33'])).
% 0.45/0.63  thf('35', plain,
% 0.45/0.63      (![X7 : $i, X8 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k7_relat_1 @ X7 @ X8)))),
% 0.45/0.63      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.45/0.63  thf('36', plain,
% 0.45/0.63      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_C)),
% 0.45/0.63      inference('demod', [status(thm)], ['17', '18'])).
% 0.45/0.63  thf('37', plain,
% 0.45/0.63      (![X7 : $i, X8 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k7_relat_1 @ X7 @ X8)))),
% 0.45/0.63      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.45/0.63  thf('38', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 0.45/0.63      inference('sup-', [status(thm)], ['21', '22'])).
% 0.45/0.63  thf('39', plain,
% 0.45/0.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.63         ((v4_relat_1 @ (k7_relat_1 @ X9 @ X10) @ X11)
% 0.45/0.63          | ~ (v4_relat_1 @ X9 @ X11)
% 0.45/0.63          | ~ (v1_relat_1 @ X9))),
% 0.45/0.63      inference('cnf', [status(esa)], [fc23_relat_1])).
% 0.45/0.63  thf('40', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ sk_D)
% 0.45/0.63          | (v4_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['38', '39'])).
% 0.45/0.63  thf('41', plain, ((v1_relat_1 @ sk_D)),
% 0.45/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.63  thf('42', plain,
% 0.45/0.63      (![X0 : $i]: (v4_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_A)),
% 0.45/0.63      inference('demod', [status(thm)], ['40', '41'])).
% 0.45/0.63  thf('43', plain,
% 0.45/0.63      (![X3 : $i, X4 : $i]:
% 0.45/0.63         (~ (v4_relat_1 @ X3 @ X4)
% 0.45/0.63          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 0.45/0.63          | ~ (v1_relat_1 @ X3))),
% 0.45/0.63      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.45/0.63  thf('44', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 0.45/0.63          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['42', '43'])).
% 0.45/0.63  thf('45', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ sk_D)
% 0.45/0.63          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['37', '44'])).
% 0.45/0.63  thf('46', plain, ((v1_relat_1 @ sk_D)),
% 0.45/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.63  thf('47', plain,
% 0.45/0.63      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_A)),
% 0.45/0.63      inference('demod', [status(thm)], ['45', '46'])).
% 0.45/0.63  thf('48', plain,
% 0.45/0.63      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.45/0.63         (~ (r1_tarski @ (k1_relat_1 @ X24) @ X25)
% 0.45/0.63          | ~ (r1_tarski @ (k2_relat_1 @ X24) @ X26)
% 0.45/0.63          | (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.45/0.63          | ~ (v1_relat_1 @ X24))),
% 0.45/0.63      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.45/0.63  thf('49', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 0.45/0.63          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.45/0.63             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.45/0.63          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['47', '48'])).
% 0.45/0.63  thf('50', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.45/0.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))
% 0.45/0.63          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['36', '49'])).
% 0.45/0.63  thf('51', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ sk_D)
% 0.45/0.63          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.45/0.63             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['35', '50'])).
% 0.45/0.63  thf('52', plain, ((v1_relat_1 @ sk_D)),
% 0.45/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.63  thf('53', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.45/0.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.45/0.63      inference('demod', [status(thm)], ['51', '52'])).
% 0.45/0.63  thf('54', plain,
% 0.45/0.63      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.45/0.63         ((v1_relat_1 @ X14)
% 0.45/0.63          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.45/0.63      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.63  thf('55', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['53', '54'])).
% 0.45/0.63  thf('56', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.45/0.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.45/0.63          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X1))),
% 0.45/0.63      inference('demod', [status(thm)], ['34', '55'])).
% 0.45/0.63  thf('57', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.45/0.63          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_C)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['19', '56'])).
% 0.45/0.63  thf('58', plain, ($false), inference('demod', [status(thm)], ['4', '57'])).
% 0.45/0.63  
% 0.45/0.63  % SZS output end Refutation
% 0.45/0.63  
% 0.47/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
