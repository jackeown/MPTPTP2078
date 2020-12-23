%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NrQR5GnexH

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 176 expanded)
%              Number of leaves         :   30 (  67 expanded)
%              Depth                    :   16
%              Number of atoms          :  622 (1459 expanded)
%              Number of equality atoms :   13 (  30 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t30_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D )
       => ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) )
          & ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
       => ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D )
         => ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) )
            & ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t30_relset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) )
    | ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) )
   <= ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('4',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_relat_1 @ sk_D ) )
   <= ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['1','4'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('6',plain,(
    ! [X19: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X18: $i] :
      ( ( r1_tarski @ X18 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X18 ) @ ( k2_relat_1 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X20: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('10',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('16',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v4_relat_1 @ X11 @ X12 )
      | ( r1_tarski @ ( k1_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('19',plain,(
    ! [X19: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X11 ) @ X12 )
      | ( v4_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_C ) @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,(
    m1_subset_1 @ ( k6_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(cc5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) )
         => ( v4_relat_1 @ C @ A ) ) ) )).

thf('26',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v4_relat_1 @ X5 @ X7 )
      | ~ ( v4_relat_1 @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc5_relat_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ~ ( v4_relat_1 @ sk_D @ X0 )
      | ( v4_relat_1 @ ( k6_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('29',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('31',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('32',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ sk_D @ X0 )
      | ( v4_relat_1 @ ( k6_relat_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( v4_relat_1 @ ( k6_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['22','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['30','31'])).

thf('36',plain,(
    v4_relat_1 @ ( k6_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v4_relat_1 @ X11 @ X12 )
      | ( r1_tarski @ ( k1_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('40',plain,(
    ! [X19: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('41',plain,(
    r1_tarski @ sk_C @ ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('43',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('44',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('46',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_D ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,(
    ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sat_resolution*',[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( r1_tarski @ sk_C @ ( k2_relat_1 @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['5','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('52',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ( v5_relat_1 @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ ( k6_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(cc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) )
         => ( v5_relat_1 @ C @ A ) ) ) )).

thf('55',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( v5_relat_1 @ X8 @ X10 )
      | ~ ( v5_relat_1 @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc6_relat_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ~ ( v5_relat_1 @ sk_D @ X0 )
      | ( v5_relat_1 @ ( k6_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['30','31'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_D @ X0 )
      | ( v5_relat_1 @ ( k6_relat_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( v5_relat_1 @ ( k6_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['30','31'])).

thf('61',plain,(
    v5_relat_1 @ ( k6_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v5_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('63',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('65',plain,(
    ! [X20: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('66',plain,(
    r1_tarski @ sk_C @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['50','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NrQR5GnexH
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:33:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 117 iterations in 0.053s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.52  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(t30_relset_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D ) =>
% 0.20/0.52         ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) ) & 
% 0.20/0.52           ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52          ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D ) =>
% 0.20/0.52            ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) ) & 
% 0.20/0.52              ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t30_relset_1])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      ((~ (r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D))
% 0.20/0.52        | ~ (r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      ((~ (r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D)))
% 0.20/0.52         <= (~ ((r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.52         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 0.20/0.52          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.52  thf('4', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      ((~ (r1_tarski @ sk_C @ (k2_relat_1 @ sk_D)))
% 0.20/0.52         <= (~ ((r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D))))),
% 0.20/0.52      inference('demod', [status(thm)], ['1', '4'])).
% 0.20/0.52  thf(t71_relat_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.20/0.52       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.52  thf('6', plain, (![X19 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 0.20/0.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.52  thf(t21_relat_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ A ) =>
% 0.20/0.52       ( r1_tarski @
% 0.20/0.52         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X18 : $i]:
% 0.20/0.52         ((r1_tarski @ X18 @ 
% 0.20/0.52           (k2_zfmisc_1 @ (k1_relat_1 @ X18) @ (k2_relat_1 @ X18)))
% 0.20/0.52          | ~ (v1_relat_1 @ X18))),
% 0.20/0.52      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r1_tarski @ (k6_relat_1 @ X0) @ 
% 0.20/0.52           (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ (k6_relat_1 @ X0))))
% 0.20/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['6', '7'])).
% 0.20/0.52  thf('9', plain, (![X20 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 0.20/0.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.52  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.20/0.52  thf('10', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X0 : $i]: (r1_tarski @ (k6_relat_1 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.20/0.52  thf(t3_subset, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X0 : $i, X2 : $i]:
% 0.20/0.52         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (m1_subset_1 @ (k6_relat_1 @ X0) @ 
% 0.20/0.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.52  thf(cc2_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.52         ((v4_relat_1 @ X21 @ X22)
% 0.20/0.52          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.20/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.52  thf('15', plain, (![X0 : $i]: (v4_relat_1 @ (k6_relat_1 @ X0) @ X0)),
% 0.20/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.52  thf(d18_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ B ) =>
% 0.20/0.52       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X11 : $i, X12 : $i]:
% 0.20/0.52         (~ (v4_relat_1 @ X11 @ X12)
% 0.20/0.52          | (r1_tarski @ (k1_relat_1 @ X11) @ X12)
% 0.20/0.52          | ~ (v1_relat_1 @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.52          | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.52  thf('18', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.52  thf('19', plain, (![X19 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 0.20/0.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.52  thf('20', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.20/0.52      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X11 : $i, X12 : $i]:
% 0.20/0.52         (~ (r1_tarski @ (k1_relat_1 @ X11) @ X12)
% 0.20/0.52          | (v4_relat_1 @ X11 @ X12)
% 0.20/0.52          | ~ (v1_relat_1 @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.52  thf('23', plain, ((r1_tarski @ (k6_relat_1 @ sk_C) @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X0 : $i, X2 : $i]:
% 0.20/0.52         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      ((m1_subset_1 @ (k6_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.52  thf(cc5_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.52       ( ![C:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) ) => ( v4_relat_1 @ C @ A ) ) ) ))).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.20/0.52          | (v4_relat_1 @ X5 @ X7)
% 0.20/0.52          | ~ (v4_relat_1 @ X6 @ X7)
% 0.20/0.52          | ~ (v1_relat_1 @ X6))),
% 0.20/0.52      inference('cnf', [status(esa)], [cc5_relat_1])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ sk_D)
% 0.20/0.52          | ~ (v4_relat_1 @ sk_D @ X0)
% 0.20/0.52          | (v4_relat_1 @ (k6_relat_1 @ sk_C) @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(cc2_relat_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (![X3 : $i, X4 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.20/0.52          | (v1_relat_1 @ X3)
% 0.20/0.52          | ~ (v1_relat_1 @ X4))),
% 0.20/0.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.52  thf(fc6_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.52  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.52      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v4_relat_1 @ sk_D @ X0) | (v4_relat_1 @ (k6_relat_1 @ sk_C) @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['27', '32'])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      ((~ (v1_relat_1 @ sk_D)
% 0.20/0.52        | (v4_relat_1 @ (k6_relat_1 @ sk_C) @ (k1_relat_1 @ sk_D)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['22', '33'])).
% 0.20/0.52  thf('35', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.52      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.52  thf('36', plain, ((v4_relat_1 @ (k6_relat_1 @ sk_C) @ (k1_relat_1 @ sk_D))),
% 0.20/0.52      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (![X11 : $i, X12 : $i]:
% 0.20/0.52         (~ (v4_relat_1 @ X11 @ X12)
% 0.20/0.52          | (r1_tarski @ (k1_relat_1 @ X11) @ X12)
% 0.20/0.52          | ~ (v1_relat_1 @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_C))
% 0.20/0.52        | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ sk_C)) @ (k1_relat_1 @ sk_D)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.52  thf('39', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.52  thf('40', plain, (![X19 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 0.20/0.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.52  thf('41', plain, ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_D))),
% 0.20/0.52      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.52         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 0.20/0.52          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      ((~ (r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D)))
% 0.20/0.52         <= (~ ((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      ((~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_D)))
% 0.20/0.52         <= (~ ((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.52  thf('47', plain, (((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['41', '46'])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      (~ ((r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D))) | 
% 0.20/0.52       ~ ((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('49', plain,
% 0.20/0.52      (~ ((r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['47', '48'])).
% 0.20/0.52  thf('50', plain, (~ (r1_tarski @ sk_C @ (k2_relat_1 @ sk_D))),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['5', '49'])).
% 0.20/0.52  thf('51', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.20/0.52      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.20/0.52  thf(d19_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ B ) =>
% 0.20/0.52       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.52  thf('52', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i]:
% 0.20/0.52         (~ (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 0.20/0.52          | (v5_relat_1 @ X13 @ X14)
% 0.20/0.52          | ~ (v1_relat_1 @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.20/0.52  thf('53', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.52  thf('54', plain,
% 0.20/0.52      ((m1_subset_1 @ (k6_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.52  thf(cc6_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.20/0.52       ( ![C:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) ) => ( v5_relat_1 @ C @ A ) ) ) ))).
% 0.20/0.52  thf('55', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.20/0.52          | (v5_relat_1 @ X8 @ X10)
% 0.20/0.52          | ~ (v5_relat_1 @ X9 @ X10)
% 0.20/0.52          | ~ (v1_relat_1 @ X9))),
% 0.20/0.52      inference('cnf', [status(esa)], [cc6_relat_1])).
% 0.20/0.52  thf('56', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ sk_D)
% 0.20/0.52          | ~ (v5_relat_1 @ sk_D @ X0)
% 0.20/0.52          | (v5_relat_1 @ (k6_relat_1 @ sk_C) @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.52  thf('57', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.52      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.52  thf('58', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v5_relat_1 @ sk_D @ X0) | (v5_relat_1 @ (k6_relat_1 @ sk_C) @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['56', '57'])).
% 0.20/0.52  thf('59', plain,
% 0.20/0.52      ((~ (v1_relat_1 @ sk_D)
% 0.20/0.52        | (v5_relat_1 @ (k6_relat_1 @ sk_C) @ (k2_relat_1 @ sk_D)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['53', '58'])).
% 0.20/0.52  thf('60', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.52      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.52  thf('61', plain, ((v5_relat_1 @ (k6_relat_1 @ sk_C) @ (k2_relat_1 @ sk_D))),
% 0.20/0.52      inference('demod', [status(thm)], ['59', '60'])).
% 0.20/0.52  thf('62', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i]:
% 0.20/0.52         (~ (v5_relat_1 @ X13 @ X14)
% 0.20/0.52          | (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 0.20/0.52          | ~ (v1_relat_1 @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.20/0.52  thf('63', plain,
% 0.20/0.52      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_C))
% 0.20/0.52        | (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ sk_C)) @ (k2_relat_1 @ sk_D)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['61', '62'])).
% 0.20/0.52  thf('64', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.52  thf('65', plain, (![X20 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 0.20/0.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.52  thf('66', plain, ((r1_tarski @ sk_C @ (k2_relat_1 @ sk_D))),
% 0.20/0.52      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.20/0.52  thf('67', plain, ($false), inference('demod', [status(thm)], ['50', '66'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
