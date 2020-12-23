%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.82G5Xclhyy

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:14 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 125 expanded)
%              Number of leaves         :   25 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :  576 (1003 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relset_1_type,type,(
    k5_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( ( k5_relset_1 @ X22 @ X23 @ X21 @ X24 )
        = ( k7_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k5_relset_1 @ sk_A @ sk_C @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t194_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) @ X11 ) ),
    inference(cnf,[status(esa)],[t194_relat_1])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( r1_tarski @ ( k2_relat_1 @ X13 ) @ ( k2_relat_1 @ X12 ) )
      | ~ ( r1_tarski @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('17',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['10','15','16'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference('sup-',[status(thm)],['5','19'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X16 @ X17 ) @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( r1_tarski @ ( k2_relat_1 @ X13 ) @ ( k2_relat_1 @ X12 ) )
      | ~ ( r1_tarski @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X16 @ X17 ) @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('26',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['24','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_C )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['20','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('37',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('38',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X25 ) @ X26 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X25 ) @ X27 )
      | ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('42',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X16 @ X17 ) @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('49',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('50',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('53',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['40','51','52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['4','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.82G5Xclhyy
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:38:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.37/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.61  % Solved by: fo/fo7.sh
% 0.37/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.61  % done 323 iterations in 0.170s
% 0.37/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.61  % SZS output start Refutation
% 0.37/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.61  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.37/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.61  thf(k5_relset_1_type, type, k5_relset_1: $i > $i > $i > $i > $i).
% 0.37/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.61  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.61  thf(t33_relset_1, conjecture,
% 0.37/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.61     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.37/0.61       ( m1_subset_1 @
% 0.37/0.61         ( k5_relset_1 @ A @ C @ D @ B ) @ 
% 0.37/0.61         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.37/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.61    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.61        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.37/0.61          ( m1_subset_1 @
% 0.37/0.61            ( k5_relset_1 @ A @ C @ D @ B ) @ 
% 0.37/0.61            ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )),
% 0.37/0.61    inference('cnf.neg', [status(esa)], [t33_relset_1])).
% 0.37/0.61  thf('0', plain,
% 0.37/0.61      (~ (m1_subset_1 @ (k5_relset_1 @ sk_A @ sk_C @ sk_D @ sk_B) @ 
% 0.37/0.61          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('1', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(redefinition_k5_relset_1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.61       ( ( k5_relset_1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.37/0.61  thf('2', plain,
% 0.37/0.61      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.37/0.61          | ((k5_relset_1 @ X22 @ X23 @ X21 @ X24) = (k7_relat_1 @ X21 @ X24)))),
% 0.37/0.61      inference('cnf', [status(esa)], [redefinition_k5_relset_1])).
% 0.37/0.61  thf('3', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((k5_relset_1 @ sk_A @ sk_C @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.61  thf('4', plain,
% 0.37/0.61      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_B) @ 
% 0.37/0.61          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.37/0.61      inference('demod', [status(thm)], ['0', '3'])).
% 0.37/0.61  thf(t194_relat_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]: ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ))).
% 0.37/0.61  thf('5', plain,
% 0.37/0.61      (![X10 : $i, X11 : $i]:
% 0.37/0.61         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X10 @ X11)) @ X11)),
% 0.37/0.61      inference('cnf', [status(esa)], [t194_relat_1])).
% 0.37/0.61  thf('6', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(t3_subset, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.61  thf('7', plain,
% 0.37/0.61      (![X3 : $i, X4 : $i]:
% 0.37/0.61         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.61  thf('8', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.37/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.61  thf(t25_relat_1, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( v1_relat_1 @ A ) =>
% 0.37/0.61       ( ![B:$i]:
% 0.37/0.61         ( ( v1_relat_1 @ B ) =>
% 0.37/0.61           ( ( r1_tarski @ A @ B ) =>
% 0.37/0.61             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.37/0.61               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.37/0.61  thf('9', plain,
% 0.37/0.61      (![X12 : $i, X13 : $i]:
% 0.37/0.61         (~ (v1_relat_1 @ X12)
% 0.37/0.61          | (r1_tarski @ (k2_relat_1 @ X13) @ (k2_relat_1 @ X12))
% 0.37/0.61          | ~ (r1_tarski @ X13 @ X12)
% 0.37/0.61          | ~ (v1_relat_1 @ X13))),
% 0.37/0.61      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.37/0.61  thf('10', plain,
% 0.37/0.61      ((~ (v1_relat_1 @ sk_D)
% 0.37/0.61        | (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 0.37/0.61           (k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))
% 0.37/0.61        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.61  thf('11', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(cc2_relat_1, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( v1_relat_1 @ A ) =>
% 0.37/0.61       ( ![B:$i]:
% 0.37/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.37/0.61  thf('12', plain,
% 0.37/0.61      (![X6 : $i, X7 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.37/0.61          | (v1_relat_1 @ X6)
% 0.37/0.61          | ~ (v1_relat_1 @ X7))),
% 0.37/0.61      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.37/0.61  thf('13', plain,
% 0.37/0.61      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)) | (v1_relat_1 @ sk_D))),
% 0.37/0.61      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.61  thf(fc6_relat_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.37/0.61  thf('14', plain,
% 0.37/0.61      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.37/0.61      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.37/0.61  thf('15', plain, ((v1_relat_1 @ sk_D)),
% 0.37/0.61      inference('demod', [status(thm)], ['13', '14'])).
% 0.37/0.61  thf('16', plain,
% 0.37/0.61      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.37/0.61      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.37/0.61  thf('17', plain,
% 0.37/0.61      ((r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 0.37/0.61        (k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.37/0.61      inference('demod', [status(thm)], ['10', '15', '16'])).
% 0.37/0.61  thf(t1_xboole_1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.37/0.61       ( r1_tarski @ A @ C ) ))).
% 0.37/0.61  thf('18', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         (~ (r1_tarski @ X0 @ X1)
% 0.37/0.61          | ~ (r1_tarski @ X1 @ X2)
% 0.37/0.61          | (r1_tarski @ X0 @ X2))),
% 0.37/0.61      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.37/0.61  thf('19', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((r1_tarski @ (k2_relat_1 @ sk_D) @ X0)
% 0.37/0.61          | ~ (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)) @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.61  thf('20', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.37/0.61      inference('sup-', [status(thm)], ['5', '19'])).
% 0.37/0.61  thf(t88_relat_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.37/0.61  thf('21', plain,
% 0.37/0.61      (![X16 : $i, X17 : $i]:
% 0.37/0.61         ((r1_tarski @ (k7_relat_1 @ X16 @ X17) @ X16) | ~ (v1_relat_1 @ X16))),
% 0.37/0.61      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.37/0.61  thf('22', plain,
% 0.37/0.61      (![X12 : $i, X13 : $i]:
% 0.37/0.61         (~ (v1_relat_1 @ X12)
% 0.37/0.61          | (r1_tarski @ (k2_relat_1 @ X13) @ (k2_relat_1 @ X12))
% 0.37/0.61          | ~ (r1_tarski @ X13 @ X12)
% 0.37/0.61          | ~ (v1_relat_1 @ X13))),
% 0.37/0.61      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.37/0.61  thf('23', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (~ (v1_relat_1 @ X0)
% 0.37/0.61          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.37/0.61          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 0.37/0.61             (k2_relat_1 @ X0))
% 0.37/0.61          | ~ (v1_relat_1 @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.61  thf('24', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 0.37/0.61           (k2_relat_1 @ X0))
% 0.37/0.61          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.37/0.61          | ~ (v1_relat_1 @ X0))),
% 0.37/0.61      inference('simplify', [status(thm)], ['23'])).
% 0.37/0.61  thf('25', plain,
% 0.37/0.61      (![X16 : $i, X17 : $i]:
% 0.37/0.61         ((r1_tarski @ (k7_relat_1 @ X16 @ X17) @ X16) | ~ (v1_relat_1 @ X16))),
% 0.37/0.61      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.37/0.61  thf('26', plain,
% 0.37/0.61      (![X3 : $i, X5 : $i]:
% 0.37/0.61         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.37/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.61  thf('27', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (~ (v1_relat_1 @ X0)
% 0.37/0.61          | (m1_subset_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['25', '26'])).
% 0.37/0.61  thf('28', plain,
% 0.37/0.61      (![X6 : $i, X7 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.37/0.61          | (v1_relat_1 @ X6)
% 0.37/0.61          | ~ (v1_relat_1 @ X7))),
% 0.37/0.61      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.37/0.61  thf('29', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (~ (v1_relat_1 @ X0)
% 0.37/0.61          | ~ (v1_relat_1 @ X0)
% 0.37/0.61          | (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['27', '28'])).
% 0.37/0.61  thf('30', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         ((v1_relat_1 @ (k7_relat_1 @ X0 @ X1)) | ~ (v1_relat_1 @ X0))),
% 0.37/0.61      inference('simplify', [status(thm)], ['29'])).
% 0.37/0.61  thf('31', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (~ (v1_relat_1 @ X0)
% 0.37/0.61          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 0.37/0.61             (k2_relat_1 @ X0)))),
% 0.37/0.61      inference('clc', [status(thm)], ['24', '30'])).
% 0.37/0.61  thf('32', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         (~ (r1_tarski @ X0 @ X1)
% 0.37/0.61          | ~ (r1_tarski @ X1 @ X2)
% 0.37/0.61          | (r1_tarski @ X0 @ X2))),
% 0.37/0.61      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.37/0.61  thf('33', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         (~ (v1_relat_1 @ X0)
% 0.37/0.61          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ X2)
% 0.37/0.61          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X2))),
% 0.37/0.61      inference('sup-', [status(thm)], ['31', '32'])).
% 0.37/0.61  thf('34', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_C)
% 0.37/0.61          | ~ (v1_relat_1 @ sk_D))),
% 0.37/0.61      inference('sup-', [status(thm)], ['20', '33'])).
% 0.37/0.61  thf('35', plain, ((v1_relat_1 @ sk_D)),
% 0.37/0.61      inference('demod', [status(thm)], ['13', '14'])).
% 0.37/0.61  thf('36', plain,
% 0.37/0.61      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_C)),
% 0.37/0.61      inference('demod', [status(thm)], ['34', '35'])).
% 0.37/0.61  thf(t87_relat_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( v1_relat_1 @ B ) =>
% 0.37/0.61       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.37/0.61  thf('37', plain,
% 0.37/0.61      (![X14 : $i, X15 : $i]:
% 0.37/0.61         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X14 @ X15)) @ X15)
% 0.37/0.61          | ~ (v1_relat_1 @ X14))),
% 0.37/0.61      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.37/0.61  thf(t11_relset_1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( v1_relat_1 @ C ) =>
% 0.37/0.61       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.37/0.61           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.37/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.37/0.61  thf('38', plain,
% 0.37/0.61      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.37/0.61         (~ (r1_tarski @ (k1_relat_1 @ X25) @ X26)
% 0.37/0.61          | ~ (r1_tarski @ (k2_relat_1 @ X25) @ X27)
% 0.37/0.61          | (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.37/0.61          | ~ (v1_relat_1 @ X25))),
% 0.37/0.61      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.37/0.61  thf('39', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         (~ (v1_relat_1 @ X1)
% 0.37/0.61          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.37/0.61          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.37/0.61             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 0.37/0.61          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))),
% 0.37/0.61      inference('sup-', [status(thm)], ['37', '38'])).
% 0.37/0.61  thf('40', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.37/0.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_C)))
% 0.37/0.61          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 0.37/0.61          | ~ (v1_relat_1 @ sk_D))),
% 0.37/0.61      inference('sup-', [status(thm)], ['36', '39'])).
% 0.37/0.61  thf('41', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.37/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.61  thf('42', plain,
% 0.37/0.61      (![X16 : $i, X17 : $i]:
% 0.37/0.61         ((r1_tarski @ (k7_relat_1 @ X16 @ X17) @ X16) | ~ (v1_relat_1 @ X16))),
% 0.37/0.61      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.37/0.61  thf('43', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         (~ (r1_tarski @ X0 @ X1)
% 0.37/0.61          | ~ (r1_tarski @ X1 @ X2)
% 0.37/0.61          | (r1_tarski @ X0 @ X2))),
% 0.37/0.61      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.37/0.61  thf('44', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         (~ (v1_relat_1 @ X0)
% 0.37/0.61          | (r1_tarski @ (k7_relat_1 @ X0 @ X1) @ X2)
% 0.37/0.61          | ~ (r1_tarski @ X0 @ X2))),
% 0.37/0.61      inference('sup-', [status(thm)], ['42', '43'])).
% 0.37/0.61  thf('45', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_C))
% 0.37/0.61          | ~ (v1_relat_1 @ sk_D))),
% 0.37/0.61      inference('sup-', [status(thm)], ['41', '44'])).
% 0.37/0.61  thf('46', plain, ((v1_relat_1 @ sk_D)),
% 0.37/0.61      inference('demod', [status(thm)], ['13', '14'])).
% 0.37/0.61  thf('47', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.37/0.61      inference('demod', [status(thm)], ['45', '46'])).
% 0.37/0.61  thf('48', plain,
% 0.37/0.61      (![X3 : $i, X5 : $i]:
% 0.37/0.61         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.37/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.61  thf('49', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.37/0.61          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['47', '48'])).
% 0.37/0.61  thf(cc1_relset_1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.61       ( v1_relat_1 @ C ) ))).
% 0.37/0.61  thf('50', plain,
% 0.37/0.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.37/0.61         ((v1_relat_1 @ X18)
% 0.37/0.61          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.37/0.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.37/0.61  thf('51', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['49', '50'])).
% 0.37/0.61  thf('52', plain, ((v1_relat_1 @ sk_D)),
% 0.37/0.61      inference('demod', [status(thm)], ['13', '14'])).
% 0.37/0.61  thf('53', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.37/0.61          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_C)))),
% 0.37/0.61      inference('demod', [status(thm)], ['40', '51', '52'])).
% 0.37/0.61  thf('54', plain, ($false), inference('demod', [status(thm)], ['4', '53'])).
% 0.37/0.61  
% 0.37/0.61  % SZS output end Refutation
% 0.37/0.61  
% 0.37/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
