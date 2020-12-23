%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2XirwNDaXI

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:14 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 134 expanded)
%              Number of leaves         :   26 (  50 expanded)
%              Depth                    :   13
%              Number of atoms          :  605 (1139 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k5_relset_1_type,type,(
    k5_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k5_relset_1 @ X26 @ X27 @ X25 @ X28 )
        = ( k7_relat_1 @ X25 @ X28 ) ) ) ),
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

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X19 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('7',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('10',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_D ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['7','10'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t89_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) ) @ ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

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
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('19',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('20',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['17','20'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ( ( k7_relat_1 @ X14 @ X15 )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_A )
        = ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('27',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X10 @ X11 ) @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['18','19'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_A )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['23','36'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('38',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X10 @ X11 ) @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('42',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('44',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(clc,[status(thm)],['40','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['37','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['18','19'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('52',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X36 ) @ X37 )
      | ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['4','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2XirwNDaXI
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:23:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.38/1.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.38/1.61  % Solved by: fo/fo7.sh
% 1.38/1.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.38/1.61  % done 1887 iterations in 1.155s
% 1.38/1.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.38/1.61  % SZS output start Refutation
% 1.38/1.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.38/1.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.38/1.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.38/1.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.38/1.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.38/1.61  thf(sk_B_type, type, sk_B: $i).
% 1.38/1.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.38/1.61  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.38/1.61  thf(k5_relset_1_type, type, k5_relset_1: $i > $i > $i > $i > $i).
% 1.38/1.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.38/1.61  thf(sk_C_type, type, sk_C: $i).
% 1.38/1.61  thf(sk_D_type, type, sk_D: $i).
% 1.38/1.61  thf(sk_A_type, type, sk_A: $i).
% 1.38/1.61  thf(t33_relset_1, conjecture,
% 1.38/1.61    (![A:$i,B:$i,C:$i,D:$i]:
% 1.38/1.61     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 1.38/1.61       ( m1_subset_1 @
% 1.38/1.61         ( k5_relset_1 @ A @ C @ D @ B ) @ 
% 1.38/1.61         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 1.38/1.61  thf(zf_stmt_0, negated_conjecture,
% 1.38/1.61    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.38/1.61        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 1.38/1.61          ( m1_subset_1 @
% 1.38/1.61            ( k5_relset_1 @ A @ C @ D @ B ) @ 
% 1.38/1.61            ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )),
% 1.38/1.61    inference('cnf.neg', [status(esa)], [t33_relset_1])).
% 1.38/1.61  thf('0', plain,
% 1.38/1.61      (~ (m1_subset_1 @ (k5_relset_1 @ sk_A @ sk_C @ sk_D @ sk_B) @ 
% 1.38/1.61          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.38/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.61  thf('1', plain,
% 1.38/1.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.38/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.61  thf(redefinition_k5_relset_1, axiom,
% 1.38/1.61    (![A:$i,B:$i,C:$i,D:$i]:
% 1.38/1.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.38/1.61       ( ( k5_relset_1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 1.38/1.61  thf('2', plain,
% 1.38/1.61      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.38/1.61         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.38/1.61          | ((k5_relset_1 @ X26 @ X27 @ X25 @ X28) = (k7_relat_1 @ X25 @ X28)))),
% 1.38/1.61      inference('cnf', [status(esa)], [redefinition_k5_relset_1])).
% 1.38/1.61  thf('3', plain,
% 1.38/1.61      (![X0 : $i]:
% 1.38/1.61         ((k5_relset_1 @ sk_A @ sk_C @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 1.38/1.61      inference('sup-', [status(thm)], ['1', '2'])).
% 1.38/1.61  thf('4', plain,
% 1.38/1.61      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_B) @ 
% 1.38/1.61          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.38/1.61      inference('demod', [status(thm)], ['0', '3'])).
% 1.38/1.61  thf('5', plain,
% 1.38/1.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.38/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.61  thf(dt_k1_relset_1, axiom,
% 1.38/1.61    (![A:$i,B:$i,C:$i]:
% 1.38/1.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.38/1.61       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.38/1.61  thf('6', plain,
% 1.38/1.61      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.38/1.61         ((m1_subset_1 @ (k1_relset_1 @ X19 @ X20 @ X21) @ (k1_zfmisc_1 @ X19))
% 1.38/1.61          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.38/1.61      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 1.38/1.61  thf('7', plain,
% 1.38/1.61      ((m1_subset_1 @ (k1_relset_1 @ sk_A @ sk_C @ sk_D) @ (k1_zfmisc_1 @ sk_A))),
% 1.38/1.61      inference('sup-', [status(thm)], ['5', '6'])).
% 1.38/1.61  thf('8', plain,
% 1.38/1.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.38/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.61  thf(redefinition_k1_relset_1, axiom,
% 1.38/1.61    (![A:$i,B:$i,C:$i]:
% 1.38/1.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.38/1.61       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.38/1.61  thf('9', plain,
% 1.38/1.61      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.38/1.61         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 1.38/1.61          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.38/1.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.38/1.61  thf('10', plain,
% 1.38/1.61      (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.38/1.61      inference('sup-', [status(thm)], ['8', '9'])).
% 1.38/1.61  thf('11', plain,
% 1.38/1.61      ((m1_subset_1 @ (k1_relat_1 @ sk_D) @ (k1_zfmisc_1 @ sk_A))),
% 1.38/1.61      inference('demod', [status(thm)], ['7', '10'])).
% 1.38/1.61  thf(t3_subset, axiom,
% 1.38/1.61    (![A:$i,B:$i]:
% 1.38/1.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.38/1.61  thf('12', plain,
% 1.38/1.61      (![X3 : $i, X4 : $i]:
% 1.38/1.61         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 1.38/1.61      inference('cnf', [status(esa)], [t3_subset])).
% 1.38/1.61  thf('13', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A)),
% 1.38/1.61      inference('sup-', [status(thm)], ['11', '12'])).
% 1.38/1.61  thf(t89_relat_1, axiom,
% 1.38/1.61    (![A:$i,B:$i]:
% 1.38/1.61     ( ( v1_relat_1 @ B ) =>
% 1.38/1.61       ( r1_tarski @
% 1.38/1.61         ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ))).
% 1.38/1.61  thf('14', plain,
% 1.38/1.61      (![X12 : $i, X13 : $i]:
% 1.38/1.61         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X12 @ X13)) @ 
% 1.38/1.61           (k1_relat_1 @ X12))
% 1.38/1.61          | ~ (v1_relat_1 @ X12))),
% 1.38/1.61      inference('cnf', [status(esa)], [t89_relat_1])).
% 1.38/1.61  thf(t1_xboole_1, axiom,
% 1.38/1.61    (![A:$i,B:$i,C:$i]:
% 1.38/1.61     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.38/1.61       ( r1_tarski @ A @ C ) ))).
% 1.38/1.61  thf('15', plain,
% 1.38/1.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.61         (~ (r1_tarski @ X0 @ X1)
% 1.38/1.61          | ~ (r1_tarski @ X1 @ X2)
% 1.38/1.61          | (r1_tarski @ X0 @ X2))),
% 1.38/1.61      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.38/1.61  thf('16', plain,
% 1.38/1.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.61         (~ (v1_relat_1 @ X0)
% 1.38/1.61          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ X2)
% 1.38/1.61          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ X2))),
% 1.38/1.61      inference('sup-', [status(thm)], ['14', '15'])).
% 1.38/1.61  thf('17', plain,
% 1.38/1.61      (![X0 : $i]:
% 1.38/1.61         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_A)
% 1.38/1.61          | ~ (v1_relat_1 @ sk_D))),
% 1.38/1.61      inference('sup-', [status(thm)], ['13', '16'])).
% 1.38/1.61  thf('18', plain,
% 1.38/1.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.38/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.61  thf(cc1_relset_1, axiom,
% 1.38/1.61    (![A:$i,B:$i,C:$i]:
% 1.38/1.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.38/1.61       ( v1_relat_1 @ C ) ))).
% 1.38/1.61  thf('19', plain,
% 1.38/1.61      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.38/1.61         ((v1_relat_1 @ X16)
% 1.38/1.61          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.38/1.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.38/1.61  thf('20', plain, ((v1_relat_1 @ sk_D)),
% 1.38/1.61      inference('sup-', [status(thm)], ['18', '19'])).
% 1.38/1.61  thf('21', plain,
% 1.38/1.61      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_A)),
% 1.38/1.61      inference('demod', [status(thm)], ['17', '20'])).
% 1.38/1.61  thf(t97_relat_1, axiom,
% 1.38/1.61    (![A:$i,B:$i]:
% 1.38/1.61     ( ( v1_relat_1 @ B ) =>
% 1.38/1.61       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 1.38/1.61         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 1.38/1.61  thf('22', plain,
% 1.38/1.61      (![X14 : $i, X15 : $i]:
% 1.38/1.61         (~ (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 1.38/1.61          | ((k7_relat_1 @ X14 @ X15) = (X14))
% 1.38/1.61          | ~ (v1_relat_1 @ X14))),
% 1.38/1.61      inference('cnf', [status(esa)], [t97_relat_1])).
% 1.38/1.61  thf('23', plain,
% 1.38/1.61      (![X0 : $i]:
% 1.38/1.61         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 1.38/1.61          | ((k7_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_A)
% 1.38/1.61              = (k7_relat_1 @ sk_D @ X0)))),
% 1.38/1.61      inference('sup-', [status(thm)], ['21', '22'])).
% 1.38/1.61  thf('24', plain,
% 1.38/1.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.38/1.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.61  thf('25', plain,
% 1.38/1.61      (![X3 : $i, X4 : $i]:
% 1.38/1.61         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 1.38/1.61      inference('cnf', [status(esa)], [t3_subset])).
% 1.38/1.61  thf('26', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_C))),
% 1.38/1.61      inference('sup-', [status(thm)], ['24', '25'])).
% 1.38/1.61  thf(t88_relat_1, axiom,
% 1.38/1.61    (![A:$i,B:$i]:
% 1.38/1.61     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 1.38/1.61  thf('27', plain,
% 1.38/1.61      (![X10 : $i, X11 : $i]:
% 1.38/1.61         ((r1_tarski @ (k7_relat_1 @ X10 @ X11) @ X10) | ~ (v1_relat_1 @ X10))),
% 1.38/1.61      inference('cnf', [status(esa)], [t88_relat_1])).
% 1.38/1.61  thf('28', plain,
% 1.38/1.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.61         (~ (r1_tarski @ X0 @ X1)
% 1.38/1.61          | ~ (r1_tarski @ X1 @ X2)
% 1.38/1.61          | (r1_tarski @ X0 @ X2))),
% 1.38/1.61      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.38/1.61  thf('29', plain,
% 1.38/1.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.61         (~ (v1_relat_1 @ X0)
% 1.38/1.61          | (r1_tarski @ (k7_relat_1 @ X0 @ X1) @ X2)
% 1.38/1.61          | ~ (r1_tarski @ X0 @ X2))),
% 1.38/1.61      inference('sup-', [status(thm)], ['27', '28'])).
% 1.38/1.61  thf('30', plain,
% 1.38/1.61      (![X0 : $i]:
% 1.38/1.61         ((r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_C))
% 1.38/1.61          | ~ (v1_relat_1 @ sk_D))),
% 1.38/1.61      inference('sup-', [status(thm)], ['26', '29'])).
% 1.38/1.61  thf('31', plain, ((v1_relat_1 @ sk_D)),
% 1.38/1.61      inference('sup-', [status(thm)], ['18', '19'])).
% 1.38/1.61  thf('32', plain,
% 1.38/1.61      (![X0 : $i]:
% 1.38/1.61         (r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_C))),
% 1.38/1.61      inference('demod', [status(thm)], ['30', '31'])).
% 1.38/1.61  thf('33', plain,
% 1.38/1.61      (![X3 : $i, X5 : $i]:
% 1.38/1.61         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 1.38/1.61      inference('cnf', [status(esa)], [t3_subset])).
% 1.38/1.61  thf('34', plain,
% 1.38/1.61      (![X0 : $i]:
% 1.38/1.61         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 1.38/1.61          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.38/1.61      inference('sup-', [status(thm)], ['32', '33'])).
% 1.38/1.61  thf('35', plain,
% 1.38/1.61      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.38/1.61         ((v1_relat_1 @ X16)
% 1.38/1.61          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.38/1.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.38/1.61  thf('36', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 1.38/1.61      inference('sup-', [status(thm)], ['34', '35'])).
% 1.38/1.61  thf('37', plain,
% 1.38/1.61      (![X0 : $i]:
% 1.38/1.61         ((k7_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_A)
% 1.38/1.61           = (k7_relat_1 @ sk_D @ X0))),
% 1.38/1.61      inference('demod', [status(thm)], ['23', '36'])).
% 1.38/1.61  thf(t87_relat_1, axiom,
% 1.38/1.61    (![A:$i,B:$i]:
% 1.38/1.61     ( ( v1_relat_1 @ B ) =>
% 1.38/1.61       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 1.38/1.61  thf('38', plain,
% 1.38/1.61      (![X8 : $i, X9 : $i]:
% 1.38/1.61         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X8 @ X9)) @ X9)
% 1.38/1.61          | ~ (v1_relat_1 @ X8))),
% 1.38/1.61      inference('cnf', [status(esa)], [t87_relat_1])).
% 1.38/1.61  thf('39', plain,
% 1.38/1.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.61         (~ (v1_relat_1 @ X0)
% 1.38/1.61          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ X2)
% 1.38/1.61          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ X2))),
% 1.38/1.61      inference('sup-', [status(thm)], ['14', '15'])).
% 1.38/1.61  thf('40', plain,
% 1.38/1.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.61         (~ (v1_relat_1 @ X1)
% 1.38/1.61          | (r1_tarski @ 
% 1.38/1.61             (k1_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)) @ X0)
% 1.38/1.61          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.38/1.61      inference('sup-', [status(thm)], ['38', '39'])).
% 1.38/1.61  thf('41', plain,
% 1.38/1.61      (![X10 : $i, X11 : $i]:
% 1.38/1.61         ((r1_tarski @ (k7_relat_1 @ X10 @ X11) @ X10) | ~ (v1_relat_1 @ X10))),
% 1.38/1.61      inference('cnf', [status(esa)], [t88_relat_1])).
% 1.38/1.61  thf('42', plain,
% 1.38/1.61      (![X3 : $i, X5 : $i]:
% 1.38/1.61         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 1.38/1.61      inference('cnf', [status(esa)], [t3_subset])).
% 1.38/1.61  thf('43', plain,
% 1.38/1.61      (![X0 : $i, X1 : $i]:
% 1.38/1.61         (~ (v1_relat_1 @ X0)
% 1.38/1.61          | (m1_subset_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 1.38/1.61      inference('sup-', [status(thm)], ['41', '42'])).
% 1.38/1.61  thf(cc2_relat_1, axiom,
% 1.38/1.61    (![A:$i]:
% 1.38/1.61     ( ( v1_relat_1 @ A ) =>
% 1.38/1.61       ( ![B:$i]:
% 1.38/1.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.38/1.61  thf('44', plain,
% 1.38/1.61      (![X6 : $i, X7 : $i]:
% 1.38/1.61         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 1.38/1.61          | (v1_relat_1 @ X6)
% 1.38/1.61          | ~ (v1_relat_1 @ X7))),
% 1.38/1.61      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.38/1.61  thf('45', plain,
% 1.38/1.61      (![X0 : $i, X1 : $i]:
% 1.38/1.61         (~ (v1_relat_1 @ X0)
% 1.38/1.61          | ~ (v1_relat_1 @ X0)
% 1.38/1.61          | (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 1.38/1.61      inference('sup-', [status(thm)], ['43', '44'])).
% 1.38/1.61  thf('46', plain,
% 1.38/1.61      (![X0 : $i, X1 : $i]:
% 1.38/1.61         ((v1_relat_1 @ (k7_relat_1 @ X0 @ X1)) | ~ (v1_relat_1 @ X0))),
% 1.38/1.61      inference('simplify', [status(thm)], ['45'])).
% 1.38/1.61  thf('47', plain,
% 1.38/1.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.61         ((r1_tarski @ 
% 1.38/1.61           (k1_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)) @ X0)
% 1.38/1.61          | ~ (v1_relat_1 @ X1))),
% 1.38/1.61      inference('clc', [status(thm)], ['40', '46'])).
% 1.38/1.61  thf('48', plain,
% 1.38/1.61      (![X0 : $i]:
% 1.38/1.61         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X0)
% 1.38/1.61          | ~ (v1_relat_1 @ sk_D))),
% 1.38/1.61      inference('sup+', [status(thm)], ['37', '47'])).
% 1.38/1.61  thf('49', plain, ((v1_relat_1 @ sk_D)),
% 1.38/1.61      inference('sup-', [status(thm)], ['18', '19'])).
% 1.38/1.61  thf('50', plain,
% 1.38/1.61      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X0)),
% 1.38/1.61      inference('demod', [status(thm)], ['48', '49'])).
% 1.38/1.61  thf('51', plain,
% 1.38/1.61      (![X0 : $i]:
% 1.38/1.61         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 1.38/1.61          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.38/1.61      inference('sup-', [status(thm)], ['32', '33'])).
% 1.38/1.61  thf(t13_relset_1, axiom,
% 1.38/1.61    (![A:$i,B:$i,C:$i,D:$i]:
% 1.38/1.61     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 1.38/1.61       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 1.38/1.61         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 1.38/1.61  thf('52', plain,
% 1.38/1.61      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 1.38/1.61         (~ (r1_tarski @ (k1_relat_1 @ X36) @ X37)
% 1.38/1.61          | (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 1.38/1.61          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 1.38/1.61      inference('cnf', [status(esa)], [t13_relset_1])).
% 1.38/1.61  thf('53', plain,
% 1.38/1.61      (![X0 : $i, X1 : $i]:
% 1.38/1.61         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 1.38/1.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 1.38/1.61          | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X1))),
% 1.38/1.61      inference('sup-', [status(thm)], ['51', '52'])).
% 1.38/1.61  thf('54', plain,
% 1.38/1.61      (![X0 : $i]:
% 1.38/1.61         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 1.38/1.61          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_C)))),
% 1.38/1.61      inference('sup-', [status(thm)], ['50', '53'])).
% 1.38/1.61  thf('55', plain, ($false), inference('demod', [status(thm)], ['4', '54'])).
% 1.38/1.61  
% 1.38/1.61  % SZS output end Refutation
% 1.38/1.61  
% 1.38/1.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
