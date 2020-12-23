%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EFD11PurTL

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:18 EST 2020

% Result     : Theorem 1.07s
% Output     : Refutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 397 expanded)
%              Number of leaves         :   31 ( 131 expanded)
%              Depth                    :   23
%              Number of atoms          : 1004 (3440 expanded)
%              Number of equality atoms :   14 (  38 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_relset_1_type,type,(
    k5_relset_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k5_relset_1 @ X31 @ X32 @ X30 @ X33 )
        = ( k7_relat_1 @ X30 @ X33 ) ) ) ),
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

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('8',plain,(
    ! [X26: $i] :
      ( ( ( k7_relat_1 @ X26 @ ( k1_relat_1 @ X26 ) )
        = X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf(t89_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ) )).

thf('9',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X24 @ X25 ) ) @ ( k1_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf(t104_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ~ ( v1_relat_1 @ X19 )
      | ( r1_tarski @ ( k7_relat_1 @ X19 @ X17 ) @ ( k7_relat_1 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t104_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) @ ( k7_relat_1 @ X2 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('14',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X22 @ X23 ) ) @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t103_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k7_relat_1 @ C @ A ) ) ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X16 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X16 @ X15 ) @ X14 )
        = ( k7_relat_1 @ X16 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t103_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k7_relat_1 @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X26: $i] :
      ( ( ( k7_relat_1 @ X26 @ ( k1_relat_1 @ X26 ) )
        = X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('18',plain,(
    ! [X26: $i] :
      ( ( ( k7_relat_1 @ X26 @ ( k1_relat_1 @ X26 ) )
        = X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('19',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X22 @ X23 ) ) @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ~ ( v1_relat_1 @ X19 )
      | ( r1_tarski @ ( k7_relat_1 @ X19 @ X17 ) @ ( k7_relat_1 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t104_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('32',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ X1 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['7','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('38',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('40',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('41',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('44',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('45',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v5_relat_1 @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('47',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v5_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('50',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v5_relat_1 @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('52',plain,(
    v5_relat_1 @ sk_D @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v5_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('54',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['39','40'])).

thf('56',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('58',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X34 ) @ X35 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X34 ) @ X36 )
      | ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['56','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['39','40'])).

thf('63',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v4_relat_1 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('65',plain,(
    v4_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('66',plain,(
    ! [X20: $i,X21: $i] :
      ( ( X20
        = ( k7_relat_1 @ X20 @ X21 ) )
      | ~ ( v4_relat_1 @ X20 @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('67',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['39','40'])).

thf('69',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) @ ( k7_relat_1 @ X2 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) @ sk_D )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['39','40'])).

thf('73',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['39','40'])).

thf('74',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) @ sk_D ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_D )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['39','40'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_D )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['49','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['39','40'])).

thf('81',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_D ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('83',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['39','40'])).

thf('87',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['48','87'])).

thf('89',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X22 @ X23 ) ) @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('90',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X34 ) @ X35 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X34 ) @ X36 )
      | ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('94',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['39','40'])).

thf('95',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['4','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EFD11PurTL
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:08:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.07/1.31  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.07/1.31  % Solved by: fo/fo7.sh
% 1.07/1.31  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.07/1.31  % done 1449 iterations in 0.863s
% 1.07/1.31  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.07/1.31  % SZS output start Refutation
% 1.07/1.31  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.07/1.31  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.07/1.31  thf(sk_A_type, type, sk_A: $i).
% 1.07/1.31  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.07/1.31  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.07/1.31  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.07/1.31  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.07/1.31  thf(sk_B_type, type, sk_B: $i).
% 1.07/1.31  thf(sk_C_type, type, sk_C: $i).
% 1.07/1.31  thf(k5_relset_1_type, type, k5_relset_1: $i > $i > $i > $i > $i).
% 1.07/1.31  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.07/1.31  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.07/1.31  thf(sk_D_type, type, sk_D: $i).
% 1.07/1.31  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.07/1.31  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.07/1.31  thf(t33_relset_1, conjecture,
% 1.07/1.31    (![A:$i,B:$i,C:$i,D:$i]:
% 1.07/1.31     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 1.07/1.31       ( m1_subset_1 @
% 1.07/1.31         ( k5_relset_1 @ A @ C @ D @ B ) @ 
% 1.07/1.31         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 1.07/1.31  thf(zf_stmt_0, negated_conjecture,
% 1.07/1.31    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.07/1.31        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 1.07/1.31          ( m1_subset_1 @
% 1.07/1.31            ( k5_relset_1 @ A @ C @ D @ B ) @ 
% 1.07/1.31            ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )),
% 1.07/1.31    inference('cnf.neg', [status(esa)], [t33_relset_1])).
% 1.07/1.31  thf('0', plain,
% 1.07/1.31      (~ (m1_subset_1 @ (k5_relset_1 @ sk_A @ sk_C @ sk_D @ sk_B) @ 
% 1.07/1.31          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.07/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.31  thf('1', plain,
% 1.07/1.31      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.07/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.31  thf(redefinition_k5_relset_1, axiom,
% 1.07/1.31    (![A:$i,B:$i,C:$i,D:$i]:
% 1.07/1.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.31       ( ( k5_relset_1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 1.07/1.31  thf('2', plain,
% 1.07/1.31      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.07/1.31         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 1.07/1.31          | ((k5_relset_1 @ X31 @ X32 @ X30 @ X33) = (k7_relat_1 @ X30 @ X33)))),
% 1.07/1.31      inference('cnf', [status(esa)], [redefinition_k5_relset_1])).
% 1.07/1.31  thf('3', plain,
% 1.07/1.31      (![X0 : $i]:
% 1.07/1.31         ((k5_relset_1 @ sk_A @ sk_C @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 1.07/1.31      inference('sup-', [status(thm)], ['1', '2'])).
% 1.07/1.31  thf('4', plain,
% 1.07/1.31      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_B) @ 
% 1.07/1.31          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.07/1.31      inference('demod', [status(thm)], ['0', '3'])).
% 1.07/1.31  thf('5', plain,
% 1.07/1.31      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.07/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.31  thf(t3_subset, axiom,
% 1.07/1.31    (![A:$i,B:$i]:
% 1.07/1.31     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.07/1.31  thf('6', plain,
% 1.07/1.31      (![X3 : $i, X4 : $i]:
% 1.07/1.31         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 1.07/1.31      inference('cnf', [status(esa)], [t3_subset])).
% 1.07/1.31  thf('7', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_C))),
% 1.07/1.31      inference('sup-', [status(thm)], ['5', '6'])).
% 1.07/1.31  thf(t98_relat_1, axiom,
% 1.07/1.31    (![A:$i]:
% 1.07/1.31     ( ( v1_relat_1 @ A ) =>
% 1.07/1.31       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 1.07/1.31  thf('8', plain,
% 1.07/1.31      (![X26 : $i]:
% 1.07/1.31         (((k7_relat_1 @ X26 @ (k1_relat_1 @ X26)) = (X26))
% 1.07/1.31          | ~ (v1_relat_1 @ X26))),
% 1.07/1.31      inference('cnf', [status(esa)], [t98_relat_1])).
% 1.07/1.31  thf(t89_relat_1, axiom,
% 1.07/1.31    (![A:$i,B:$i]:
% 1.07/1.31     ( ( v1_relat_1 @ B ) =>
% 1.07/1.31       ( r1_tarski @
% 1.07/1.31         ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ))).
% 1.07/1.31  thf('9', plain,
% 1.07/1.31      (![X24 : $i, X25 : $i]:
% 1.07/1.31         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X24 @ X25)) @ 
% 1.07/1.31           (k1_relat_1 @ X24))
% 1.07/1.31          | ~ (v1_relat_1 @ X24))),
% 1.07/1.31      inference('cnf', [status(esa)], [t89_relat_1])).
% 1.07/1.31  thf(t104_relat_1, axiom,
% 1.07/1.31    (![A:$i,B:$i,C:$i]:
% 1.07/1.31     ( ( v1_relat_1 @ C ) =>
% 1.07/1.31       ( ( r1_tarski @ A @ B ) =>
% 1.07/1.31         ( r1_tarski @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ))).
% 1.07/1.31  thf('10', plain,
% 1.07/1.31      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.07/1.31         (~ (r1_tarski @ X17 @ X18)
% 1.07/1.31          | ~ (v1_relat_1 @ X19)
% 1.07/1.31          | (r1_tarski @ (k7_relat_1 @ X19 @ X17) @ (k7_relat_1 @ X19 @ X18)))),
% 1.07/1.31      inference('cnf', [status(esa)], [t104_relat_1])).
% 1.07/1.31  thf('11', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.31         (~ (v1_relat_1 @ X0)
% 1.07/1.31          | (r1_tarski @ 
% 1.07/1.31             (k7_relat_1 @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1))) @ 
% 1.07/1.31             (k7_relat_1 @ X2 @ (k1_relat_1 @ X0)))
% 1.07/1.31          | ~ (v1_relat_1 @ X2))),
% 1.07/1.31      inference('sup-', [status(thm)], ['9', '10'])).
% 1.07/1.31  thf('12', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i]:
% 1.07/1.31         ((r1_tarski @ 
% 1.07/1.31           (k7_relat_1 @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1))) @ X0)
% 1.07/1.31          | ~ (v1_relat_1 @ X0)
% 1.07/1.31          | ~ (v1_relat_1 @ X0)
% 1.07/1.31          | ~ (v1_relat_1 @ X0))),
% 1.07/1.31      inference('sup+', [status(thm)], ['8', '11'])).
% 1.07/1.31  thf('13', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i]:
% 1.07/1.31         (~ (v1_relat_1 @ X0)
% 1.07/1.31          | (r1_tarski @ 
% 1.07/1.31             (k7_relat_1 @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1))) @ X0))),
% 1.07/1.31      inference('simplify', [status(thm)], ['12'])).
% 1.07/1.31  thf(t87_relat_1, axiom,
% 1.07/1.31    (![A:$i,B:$i]:
% 1.07/1.31     ( ( v1_relat_1 @ B ) =>
% 1.07/1.31       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 1.07/1.31  thf('14', plain,
% 1.07/1.31      (![X22 : $i, X23 : $i]:
% 1.07/1.31         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X22 @ X23)) @ X23)
% 1.07/1.31          | ~ (v1_relat_1 @ X22))),
% 1.07/1.31      inference('cnf', [status(esa)], [t87_relat_1])).
% 1.07/1.31  thf(t103_relat_1, axiom,
% 1.07/1.31    (![A:$i,B:$i,C:$i]:
% 1.07/1.31     ( ( v1_relat_1 @ C ) =>
% 1.07/1.31       ( ( r1_tarski @ A @ B ) =>
% 1.07/1.31         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 1.07/1.31  thf('15', plain,
% 1.07/1.31      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.07/1.31         (~ (r1_tarski @ X14 @ X15)
% 1.07/1.31          | ~ (v1_relat_1 @ X16)
% 1.07/1.31          | ((k7_relat_1 @ (k7_relat_1 @ X16 @ X15) @ X14)
% 1.07/1.31              = (k7_relat_1 @ X16 @ X14)))),
% 1.07/1.31      inference('cnf', [status(esa)], [t103_relat_1])).
% 1.07/1.31  thf('16', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.31         (~ (v1_relat_1 @ X1)
% 1.07/1.31          | ((k7_relat_1 @ (k7_relat_1 @ X2 @ X0) @ 
% 1.07/1.31              (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.07/1.31              = (k7_relat_1 @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 1.07/1.31          | ~ (v1_relat_1 @ X2))),
% 1.07/1.31      inference('sup-', [status(thm)], ['14', '15'])).
% 1.07/1.31  thf('17', plain,
% 1.07/1.31      (![X26 : $i]:
% 1.07/1.31         (((k7_relat_1 @ X26 @ (k1_relat_1 @ X26)) = (X26))
% 1.07/1.31          | ~ (v1_relat_1 @ X26))),
% 1.07/1.31      inference('cnf', [status(esa)], [t98_relat_1])).
% 1.07/1.31  thf('18', plain,
% 1.07/1.31      (![X26 : $i]:
% 1.07/1.31         (((k7_relat_1 @ X26 @ (k1_relat_1 @ X26)) = (X26))
% 1.07/1.31          | ~ (v1_relat_1 @ X26))),
% 1.07/1.31      inference('cnf', [status(esa)], [t98_relat_1])).
% 1.07/1.31  thf('19', plain,
% 1.07/1.31      (![X22 : $i, X23 : $i]:
% 1.07/1.31         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X22 @ X23)) @ X23)
% 1.07/1.31          | ~ (v1_relat_1 @ X22))),
% 1.07/1.31      inference('cnf', [status(esa)], [t87_relat_1])).
% 1.07/1.31  thf('20', plain,
% 1.07/1.31      (![X0 : $i]:
% 1.07/1.31         ((r1_tarski @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 1.07/1.31          | ~ (v1_relat_1 @ X0)
% 1.07/1.31          | ~ (v1_relat_1 @ X0))),
% 1.07/1.31      inference('sup+', [status(thm)], ['18', '19'])).
% 1.07/1.31  thf('21', plain,
% 1.07/1.31      (![X0 : $i]:
% 1.07/1.31         (~ (v1_relat_1 @ X0)
% 1.07/1.31          | (r1_tarski @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 1.07/1.31      inference('simplify', [status(thm)], ['20'])).
% 1.07/1.31  thf('22', plain,
% 1.07/1.31      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.07/1.31         (~ (r1_tarski @ X17 @ X18)
% 1.07/1.31          | ~ (v1_relat_1 @ X19)
% 1.07/1.31          | (r1_tarski @ (k7_relat_1 @ X19 @ X17) @ (k7_relat_1 @ X19 @ X18)))),
% 1.07/1.31      inference('cnf', [status(esa)], [t104_relat_1])).
% 1.07/1.31  thf('23', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i]:
% 1.07/1.31         (~ (v1_relat_1 @ X0)
% 1.07/1.31          | (r1_tarski @ (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ 
% 1.07/1.31             (k7_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 1.07/1.31          | ~ (v1_relat_1 @ X1))),
% 1.07/1.31      inference('sup-', [status(thm)], ['21', '22'])).
% 1.07/1.31  thf('24', plain,
% 1.07/1.31      (![X0 : $i]:
% 1.07/1.31         ((r1_tarski @ X0 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 1.07/1.31          | ~ (v1_relat_1 @ X0)
% 1.07/1.31          | ~ (v1_relat_1 @ X0)
% 1.07/1.31          | ~ (v1_relat_1 @ X0))),
% 1.07/1.31      inference('sup+', [status(thm)], ['17', '23'])).
% 1.07/1.31  thf('25', plain,
% 1.07/1.31      (![X0 : $i]:
% 1.07/1.31         (~ (v1_relat_1 @ X0)
% 1.07/1.31          | (r1_tarski @ X0 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 1.07/1.31      inference('simplify', [status(thm)], ['24'])).
% 1.07/1.31  thf(t1_xboole_1, axiom,
% 1.07/1.31    (![A:$i,B:$i,C:$i]:
% 1.07/1.31     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.07/1.31       ( r1_tarski @ A @ C ) ))).
% 1.07/1.31  thf('26', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.31         (~ (r1_tarski @ X0 @ X1)
% 1.07/1.31          | ~ (r1_tarski @ X1 @ X2)
% 1.07/1.31          | (r1_tarski @ X0 @ X2))),
% 1.07/1.31      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.07/1.31  thf('27', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i]:
% 1.07/1.31         (~ (v1_relat_1 @ X0)
% 1.07/1.31          | (r1_tarski @ X0 @ X1)
% 1.07/1.31          | ~ (r1_tarski @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ X1))),
% 1.07/1.31      inference('sup-', [status(thm)], ['25', '26'])).
% 1.07/1.31  thf('28', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.31         (~ (r1_tarski @ 
% 1.07/1.31             (k7_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))) @ X2)
% 1.07/1.31          | ~ (v1_relat_1 @ X1)
% 1.07/1.31          | ~ (v1_relat_1 @ X1)
% 1.07/1.31          | (r1_tarski @ (k7_relat_1 @ X1 @ X0) @ X2)
% 1.07/1.31          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.07/1.31      inference('sup-', [status(thm)], ['16', '27'])).
% 1.07/1.31  thf('29', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.31         (~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.07/1.31          | (r1_tarski @ (k7_relat_1 @ X1 @ X0) @ X2)
% 1.07/1.31          | ~ (v1_relat_1 @ X1)
% 1.07/1.31          | ~ (r1_tarski @ 
% 1.07/1.31               (k7_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))) @ X2))),
% 1.07/1.31      inference('simplify', [status(thm)], ['28'])).
% 1.07/1.31  thf('30', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i]:
% 1.07/1.31         (~ (v1_relat_1 @ X0)
% 1.07/1.31          | ~ (v1_relat_1 @ X0)
% 1.07/1.31          | (r1_tarski @ (k7_relat_1 @ X0 @ X1) @ X0)
% 1.07/1.31          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 1.07/1.31      inference('sup-', [status(thm)], ['13', '29'])).
% 1.07/1.31  thf('31', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i]:
% 1.07/1.31         (~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 1.07/1.31          | (r1_tarski @ (k7_relat_1 @ X0 @ X1) @ X0)
% 1.07/1.31          | ~ (v1_relat_1 @ X0))),
% 1.07/1.31      inference('simplify', [status(thm)], ['30'])).
% 1.07/1.31  thf(dt_k7_relat_1, axiom,
% 1.07/1.31    (![A:$i,B:$i]:
% 1.07/1.31     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 1.07/1.31  thf('32', plain,
% 1.07/1.31      (![X10 : $i, X11 : $i]:
% 1.07/1.31         (~ (v1_relat_1 @ X10) | (v1_relat_1 @ (k7_relat_1 @ X10 @ X11)))),
% 1.07/1.31      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.07/1.31  thf('33', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i]:
% 1.07/1.31         (~ (v1_relat_1 @ X0) | (r1_tarski @ (k7_relat_1 @ X0 @ X1) @ X0))),
% 1.07/1.31      inference('clc', [status(thm)], ['31', '32'])).
% 1.07/1.31  thf('34', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.31         (~ (r1_tarski @ X0 @ X1)
% 1.07/1.31          | ~ (r1_tarski @ X1 @ X2)
% 1.07/1.31          | (r1_tarski @ X0 @ X2))),
% 1.07/1.31      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.07/1.31  thf('35', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.31         (~ (v1_relat_1 @ X0)
% 1.07/1.31          | (r1_tarski @ (k7_relat_1 @ X0 @ X1) @ X2)
% 1.07/1.31          | ~ (r1_tarski @ X0 @ X2))),
% 1.07/1.31      inference('sup-', [status(thm)], ['33', '34'])).
% 1.07/1.31  thf('36', plain,
% 1.07/1.31      (![X0 : $i]:
% 1.07/1.31         ((r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_C))
% 1.07/1.31          | ~ (v1_relat_1 @ sk_D))),
% 1.07/1.31      inference('sup-', [status(thm)], ['7', '35'])).
% 1.07/1.31  thf('37', plain,
% 1.07/1.31      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.07/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.31  thf(cc2_relat_1, axiom,
% 1.07/1.31    (![A:$i]:
% 1.07/1.31     ( ( v1_relat_1 @ A ) =>
% 1.07/1.31       ( ![B:$i]:
% 1.07/1.31         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.07/1.31  thf('38', plain,
% 1.07/1.31      (![X6 : $i, X7 : $i]:
% 1.07/1.31         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 1.07/1.31          | (v1_relat_1 @ X6)
% 1.07/1.31          | ~ (v1_relat_1 @ X7))),
% 1.07/1.31      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.07/1.31  thf('39', plain,
% 1.07/1.31      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)) | (v1_relat_1 @ sk_D))),
% 1.07/1.31      inference('sup-', [status(thm)], ['37', '38'])).
% 1.07/1.31  thf(fc6_relat_1, axiom,
% 1.07/1.31    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.07/1.31  thf('40', plain,
% 1.07/1.31      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13))),
% 1.07/1.31      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.07/1.31  thf('41', plain, ((v1_relat_1 @ sk_D)),
% 1.07/1.31      inference('demod', [status(thm)], ['39', '40'])).
% 1.07/1.31  thf('42', plain,
% 1.07/1.31      (![X0 : $i]:
% 1.07/1.31         (r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_C))),
% 1.07/1.31      inference('demod', [status(thm)], ['36', '41'])).
% 1.07/1.31  thf('43', plain,
% 1.07/1.31      (![X3 : $i, X5 : $i]:
% 1.07/1.31         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 1.07/1.31      inference('cnf', [status(esa)], [t3_subset])).
% 1.07/1.31  thf('44', plain,
% 1.07/1.31      (![X0 : $i]:
% 1.07/1.31         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 1.07/1.31          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.07/1.31      inference('sup-', [status(thm)], ['42', '43'])).
% 1.07/1.31  thf(cc2_relset_1, axiom,
% 1.07/1.31    (![A:$i,B:$i,C:$i]:
% 1.07/1.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.31       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.07/1.31  thf('45', plain,
% 1.07/1.31      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.07/1.31         ((v5_relat_1 @ X27 @ X29)
% 1.07/1.31          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 1.07/1.31      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.07/1.31  thf('46', plain,
% 1.07/1.31      (![X0 : $i]: (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_C)),
% 1.07/1.31      inference('sup-', [status(thm)], ['44', '45'])).
% 1.07/1.31  thf(d19_relat_1, axiom,
% 1.07/1.31    (![A:$i,B:$i]:
% 1.07/1.31     ( ( v1_relat_1 @ B ) =>
% 1.07/1.31       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.07/1.31  thf('47', plain,
% 1.07/1.31      (![X8 : $i, X9 : $i]:
% 1.07/1.31         (~ (v5_relat_1 @ X8 @ X9)
% 1.07/1.31          | (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 1.07/1.31          | ~ (v1_relat_1 @ X8))),
% 1.07/1.31      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.07/1.31  thf('48', plain,
% 1.07/1.31      (![X0 : $i]:
% 1.07/1.31         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 1.07/1.31          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_C))),
% 1.07/1.31      inference('sup-', [status(thm)], ['46', '47'])).
% 1.07/1.31  thf('49', plain,
% 1.07/1.31      (![X10 : $i, X11 : $i]:
% 1.07/1.31         (~ (v1_relat_1 @ X10) | (v1_relat_1 @ (k7_relat_1 @ X10 @ X11)))),
% 1.07/1.31      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.07/1.31  thf('50', plain,
% 1.07/1.31      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.07/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.31  thf('51', plain,
% 1.07/1.31      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.07/1.31         ((v5_relat_1 @ X27 @ X29)
% 1.07/1.31          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 1.07/1.31      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.07/1.31  thf('52', plain, ((v5_relat_1 @ sk_D @ sk_C)),
% 1.07/1.31      inference('sup-', [status(thm)], ['50', '51'])).
% 1.07/1.31  thf('53', plain,
% 1.07/1.31      (![X8 : $i, X9 : $i]:
% 1.07/1.31         (~ (v5_relat_1 @ X8 @ X9)
% 1.07/1.31          | (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 1.07/1.31          | ~ (v1_relat_1 @ X8))),
% 1.07/1.31      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.07/1.31  thf('54', plain,
% 1.07/1.31      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C))),
% 1.07/1.31      inference('sup-', [status(thm)], ['52', '53'])).
% 1.07/1.31  thf('55', plain, ((v1_relat_1 @ sk_D)),
% 1.07/1.31      inference('demod', [status(thm)], ['39', '40'])).
% 1.07/1.31  thf('56', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 1.07/1.31      inference('demod', [status(thm)], ['54', '55'])).
% 1.07/1.31  thf('57', plain,
% 1.07/1.31      (![X0 : $i]:
% 1.07/1.31         (~ (v1_relat_1 @ X0)
% 1.07/1.31          | (r1_tarski @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 1.07/1.31      inference('simplify', [status(thm)], ['20'])).
% 1.07/1.31  thf(t11_relset_1, axiom,
% 1.07/1.31    (![A:$i,B:$i,C:$i]:
% 1.07/1.31     ( ( v1_relat_1 @ C ) =>
% 1.07/1.31       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 1.07/1.31           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 1.07/1.31         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 1.07/1.31  thf('58', plain,
% 1.07/1.31      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.07/1.31         (~ (r1_tarski @ (k1_relat_1 @ X34) @ X35)
% 1.07/1.31          | ~ (r1_tarski @ (k2_relat_1 @ X34) @ X36)
% 1.07/1.31          | (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 1.07/1.31          | ~ (v1_relat_1 @ X34))),
% 1.07/1.31      inference('cnf', [status(esa)], [t11_relset_1])).
% 1.07/1.31  thf('59', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i]:
% 1.07/1.31         (~ (v1_relat_1 @ X0)
% 1.07/1.31          | ~ (v1_relat_1 @ X0)
% 1.07/1.31          | (m1_subset_1 @ X0 @ 
% 1.07/1.31             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 1.07/1.31          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 1.07/1.31      inference('sup-', [status(thm)], ['57', '58'])).
% 1.07/1.31  thf('60', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i]:
% 1.07/1.31         (~ (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 1.07/1.31          | (m1_subset_1 @ X0 @ 
% 1.07/1.31             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 1.07/1.31          | ~ (v1_relat_1 @ X0))),
% 1.07/1.31      inference('simplify', [status(thm)], ['59'])).
% 1.07/1.31  thf('61', plain,
% 1.07/1.31      ((~ (v1_relat_1 @ sk_D)
% 1.07/1.31        | (m1_subset_1 @ sk_D @ 
% 1.07/1.31           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C))))),
% 1.07/1.31      inference('sup-', [status(thm)], ['56', '60'])).
% 1.07/1.31  thf('62', plain, ((v1_relat_1 @ sk_D)),
% 1.07/1.31      inference('demod', [status(thm)], ['39', '40'])).
% 1.07/1.31  thf('63', plain,
% 1.07/1.31      ((m1_subset_1 @ sk_D @ 
% 1.07/1.31        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C)))),
% 1.07/1.31      inference('demod', [status(thm)], ['61', '62'])).
% 1.07/1.31  thf('64', plain,
% 1.07/1.31      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.07/1.31         ((v4_relat_1 @ X27 @ X28)
% 1.07/1.31          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 1.07/1.31      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.07/1.31  thf('65', plain, ((v4_relat_1 @ sk_D @ (k1_relat_1 @ sk_D))),
% 1.07/1.31      inference('sup-', [status(thm)], ['63', '64'])).
% 1.07/1.31  thf(t209_relat_1, axiom,
% 1.07/1.31    (![A:$i,B:$i]:
% 1.07/1.31     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.07/1.31       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 1.07/1.31  thf('66', plain,
% 1.07/1.31      (![X20 : $i, X21 : $i]:
% 1.07/1.31         (((X20) = (k7_relat_1 @ X20 @ X21))
% 1.07/1.31          | ~ (v4_relat_1 @ X20 @ X21)
% 1.07/1.31          | ~ (v1_relat_1 @ X20))),
% 1.07/1.31      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.07/1.31  thf('67', plain,
% 1.07/1.31      ((~ (v1_relat_1 @ sk_D)
% 1.07/1.31        | ((sk_D) = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D))))),
% 1.07/1.31      inference('sup-', [status(thm)], ['65', '66'])).
% 1.07/1.31  thf('68', plain, ((v1_relat_1 @ sk_D)),
% 1.07/1.31      inference('demod', [status(thm)], ['39', '40'])).
% 1.07/1.31  thf('69', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))),
% 1.07/1.31      inference('demod', [status(thm)], ['67', '68'])).
% 1.07/1.31  thf('70', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.31         (~ (v1_relat_1 @ X0)
% 1.07/1.31          | (r1_tarski @ 
% 1.07/1.31             (k7_relat_1 @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1))) @ 
% 1.07/1.31             (k7_relat_1 @ X2 @ (k1_relat_1 @ X0)))
% 1.07/1.31          | ~ (v1_relat_1 @ X2))),
% 1.07/1.31      inference('sup-', [status(thm)], ['9', '10'])).
% 1.07/1.31  thf('71', plain,
% 1.07/1.31      (![X0 : $i]:
% 1.07/1.31         ((r1_tarski @ 
% 1.07/1.31           (k7_relat_1 @ sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0))) @ sk_D)
% 1.07/1.31          | ~ (v1_relat_1 @ sk_D)
% 1.07/1.31          | ~ (v1_relat_1 @ sk_D))),
% 1.07/1.31      inference('sup+', [status(thm)], ['69', '70'])).
% 1.07/1.31  thf('72', plain, ((v1_relat_1 @ sk_D)),
% 1.07/1.31      inference('demod', [status(thm)], ['39', '40'])).
% 1.07/1.31  thf('73', plain, ((v1_relat_1 @ sk_D)),
% 1.07/1.31      inference('demod', [status(thm)], ['39', '40'])).
% 1.07/1.31  thf('74', plain,
% 1.07/1.31      (![X0 : $i]:
% 1.07/1.31         (r1_tarski @ 
% 1.07/1.31          (k7_relat_1 @ sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0))) @ sk_D)),
% 1.07/1.31      inference('demod', [status(thm)], ['71', '72', '73'])).
% 1.07/1.31  thf('75', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.31         (~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.07/1.31          | (r1_tarski @ (k7_relat_1 @ X1 @ X0) @ X2)
% 1.07/1.31          | ~ (v1_relat_1 @ X1)
% 1.07/1.31          | ~ (r1_tarski @ 
% 1.07/1.31               (k7_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))) @ X2))),
% 1.07/1.31      inference('simplify', [status(thm)], ['28'])).
% 1.07/1.31  thf('76', plain,
% 1.07/1.31      (![X0 : $i]:
% 1.07/1.31         (~ (v1_relat_1 @ sk_D)
% 1.07/1.31          | (r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ sk_D)
% 1.07/1.31          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 1.07/1.31      inference('sup-', [status(thm)], ['74', '75'])).
% 1.07/1.31  thf('77', plain, ((v1_relat_1 @ sk_D)),
% 1.07/1.31      inference('demod', [status(thm)], ['39', '40'])).
% 1.07/1.31  thf('78', plain,
% 1.07/1.31      (![X0 : $i]:
% 1.07/1.31         ((r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ sk_D)
% 1.07/1.31          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 1.07/1.31      inference('demod', [status(thm)], ['76', '77'])).
% 1.07/1.31  thf('79', plain,
% 1.07/1.31      (![X0 : $i]:
% 1.07/1.31         (~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ sk_D))),
% 1.07/1.31      inference('sup-', [status(thm)], ['49', '78'])).
% 1.07/1.31  thf('80', plain, ((v1_relat_1 @ sk_D)),
% 1.07/1.31      inference('demod', [status(thm)], ['39', '40'])).
% 1.07/1.31  thf('81', plain, (![X0 : $i]: (r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ sk_D)),
% 1.07/1.31      inference('demod', [status(thm)], ['79', '80'])).
% 1.07/1.31  thf('82', plain,
% 1.07/1.31      (![X3 : $i, X5 : $i]:
% 1.07/1.31         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 1.07/1.31      inference('cnf', [status(esa)], [t3_subset])).
% 1.07/1.31  thf('83', plain,
% 1.07/1.31      (![X0 : $i]:
% 1.07/1.31         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ (k1_zfmisc_1 @ sk_D))),
% 1.07/1.31      inference('sup-', [status(thm)], ['81', '82'])).
% 1.07/1.31  thf('84', plain,
% 1.07/1.31      (![X6 : $i, X7 : $i]:
% 1.07/1.31         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 1.07/1.31          | (v1_relat_1 @ X6)
% 1.07/1.31          | ~ (v1_relat_1 @ X7))),
% 1.07/1.31      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.07/1.31  thf('85', plain,
% 1.07/1.31      (![X0 : $i]:
% 1.07/1.31         (~ (v1_relat_1 @ sk_D) | (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 1.07/1.31      inference('sup-', [status(thm)], ['83', '84'])).
% 1.07/1.31  thf('86', plain, ((v1_relat_1 @ sk_D)),
% 1.07/1.31      inference('demod', [status(thm)], ['39', '40'])).
% 1.07/1.31  thf('87', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 1.07/1.31      inference('demod', [status(thm)], ['85', '86'])).
% 1.07/1.31  thf('88', plain,
% 1.07/1.31      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_C)),
% 1.07/1.31      inference('demod', [status(thm)], ['48', '87'])).
% 1.07/1.31  thf('89', plain,
% 1.07/1.31      (![X22 : $i, X23 : $i]:
% 1.07/1.31         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X22 @ X23)) @ X23)
% 1.07/1.31          | ~ (v1_relat_1 @ X22))),
% 1.07/1.31      inference('cnf', [status(esa)], [t87_relat_1])).
% 1.07/1.31  thf('90', plain,
% 1.07/1.31      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.07/1.31         (~ (r1_tarski @ (k1_relat_1 @ X34) @ X35)
% 1.07/1.31          | ~ (r1_tarski @ (k2_relat_1 @ X34) @ X36)
% 1.07/1.31          | (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 1.07/1.31          | ~ (v1_relat_1 @ X34))),
% 1.07/1.31      inference('cnf', [status(esa)], [t11_relset_1])).
% 1.07/1.31  thf('91', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.31         (~ (v1_relat_1 @ X1)
% 1.07/1.31          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.07/1.31          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 1.07/1.31             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 1.07/1.31          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))),
% 1.07/1.31      inference('sup-', [status(thm)], ['89', '90'])).
% 1.07/1.31  thf('92', plain,
% 1.07/1.31      (![X0 : $i]:
% 1.07/1.31         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 1.07/1.31           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_C)))
% 1.07/1.31          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 1.07/1.31          | ~ (v1_relat_1 @ sk_D))),
% 1.07/1.31      inference('sup-', [status(thm)], ['88', '91'])).
% 1.07/1.31  thf('93', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 1.07/1.31      inference('demod', [status(thm)], ['85', '86'])).
% 1.07/1.31  thf('94', plain, ((v1_relat_1 @ sk_D)),
% 1.07/1.31      inference('demod', [status(thm)], ['39', '40'])).
% 1.07/1.31  thf('95', plain,
% 1.07/1.31      (![X0 : $i]:
% 1.07/1.31         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 1.07/1.31          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_C)))),
% 1.07/1.31      inference('demod', [status(thm)], ['92', '93', '94'])).
% 1.07/1.31  thf('96', plain, ($false), inference('demod', [status(thm)], ['4', '95'])).
% 1.07/1.31  
% 1.07/1.31  % SZS output end Refutation
% 1.07/1.31  
% 1.15/1.32  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
