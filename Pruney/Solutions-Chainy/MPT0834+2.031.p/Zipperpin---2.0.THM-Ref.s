%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wXiUL3GprP

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:42 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 323 expanded)
%              Number of leaves         :   37 ( 114 expanded)
%              Depth                    :   19
%              Number of atoms          :  899 (3414 expanded)
%              Number of equality atoms :   65 ( 207 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(t38_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
       => ( ( ( k7_relset_1 @ A @ B @ C @ A )
            = ( k2_relset_1 @ A @ B @ C ) )
          & ( ( k8_relset_1 @ A @ B @ C @ B )
            = ( k1_relset_1 @ A @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_relset_1])).

thf('0',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('4',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('7',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k7_relset_1 @ X33 @ X34 @ X32 @ X35 )
        = ( k9_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,
    ( ( ( k9_relat_1 @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X23 @ X24 @ X25 ) @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('13',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    r1_tarski @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('17',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v5_relat_1 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('20',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('21',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('26',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['22','27'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('29',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X18 ) @ X19 )
      | ( ( k5_relat_1 @ X18 @ ( k6_relat_1 @ X19 ) )
        = X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['25','26'])).

thf('32',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['30','31'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('33',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('34',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) )
        = ( k10_relat_1 @ X13 @ ( k1_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('35',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X17 ) @ X16 )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X2 @ X0 ) @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('38',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X2 @ X0 ) @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) )
        = ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) )
      | ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['25','26'])).

thf('42',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['25','26'])).

thf('43',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['30','31'])).

thf('44',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['30','31'])).

thf('45',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['30','31'])).

thf('46',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) )
        = ( k10_relat_1 @ X13 @ ( k1_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('47',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('49',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['25','26'])).

thf('50',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_C )
        = sk_C )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41','42','43','44','51'])).

thf('53',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['17','52'])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('54',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) )
        = ( k9_relat_1 @ X10 @ ( k2_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('55',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X15: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('57',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('58',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['25','26'])).

thf('59',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('61',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('62',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['10','59','62'])).

thf('64',plain,
    ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('66',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
 != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['64','65'])).

thf('67',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['5','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('69',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( ( k8_relset_1 @ X37 @ X38 @ X36 @ X39 )
        = ( k10_relat_1 @ X36 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('72',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['67','70','71'])).

thf('73',plain,(
    $false ),
    inference(simplify,[status(thm)],['72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wXiUL3GprP
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:16:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.60  % Solved by: fo/fo7.sh
% 0.39/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.60  % done 133 iterations in 0.140s
% 0.39/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.60  % SZS output start Refutation
% 0.39/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.60  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.39/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.60  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.39/0.60  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.39/0.60  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.39/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.60  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.39/0.60  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.39/0.60  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.39/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.60  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.39/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.60  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.39/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.60  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.39/0.60  thf(t38_relset_1, conjecture,
% 0.39/0.60    (![A:$i,B:$i,C:$i]:
% 0.39/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.60       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.39/0.60         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.39/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.60    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.60        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.60          ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.39/0.60            ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) )),
% 0.39/0.60    inference('cnf.neg', [status(esa)], [t38_relset_1])).
% 0.39/0.60  thf('0', plain,
% 0.39/0.60      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.39/0.60          != (k2_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.39/0.60        | ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.39/0.60            != (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('1', plain,
% 0.39/0.60      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.39/0.60          != (k1_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.39/0.60         <= (~
% 0.39/0.60             (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.39/0.60                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.39/0.60      inference('split', [status(esa)], ['0'])).
% 0.39/0.60  thf('2', plain,
% 0.39/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(redefinition_k1_relset_1, axiom,
% 0.39/0.60    (![A:$i,B:$i,C:$i]:
% 0.39/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.60       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.39/0.60  thf('3', plain,
% 0.39/0.60      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.39/0.60         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 0.39/0.60          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.39/0.60      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.39/0.60  thf('4', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.39/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.60  thf('5', plain,
% 0.39/0.60      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B) != (k1_relat_1 @ sk_C)))
% 0.39/0.60         <= (~
% 0.39/0.60             (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.39/0.60                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.39/0.60      inference('demod', [status(thm)], ['1', '4'])).
% 0.39/0.60  thf('6', plain,
% 0.39/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(redefinition_k7_relset_1, axiom,
% 0.39/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.60       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.39/0.60  thf('7', plain,
% 0.39/0.60      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.39/0.60         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.39/0.60          | ((k7_relset_1 @ X33 @ X34 @ X32 @ X35) = (k9_relat_1 @ X32 @ X35)))),
% 0.39/0.60      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.39/0.60  thf('8', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.60  thf('9', plain,
% 0.39/0.60      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.39/0.60          != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.39/0.60         <= (~
% 0.39/0.60             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.39/0.60                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.39/0.60      inference('split', [status(esa)], ['0'])).
% 0.39/0.60  thf('10', plain,
% 0.39/0.60      ((((k9_relat_1 @ sk_C @ sk_A) != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.39/0.60         <= (~
% 0.39/0.60             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.39/0.60                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.39/0.60      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.60  thf('11', plain,
% 0.39/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(dt_k1_relset_1, axiom,
% 0.39/0.60    (![A:$i,B:$i,C:$i]:
% 0.39/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.60       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.39/0.60  thf('12', plain,
% 0.39/0.60      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.39/0.60         ((m1_subset_1 @ (k1_relset_1 @ X23 @ X24 @ X25) @ (k1_zfmisc_1 @ X23))
% 0.39/0.60          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.39/0.60      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.39/0.60  thf('13', plain,
% 0.39/0.60      ((m1_subset_1 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.39/0.60  thf(t3_subset, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.60  thf('14', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.39/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.60  thf('15', plain, ((r1_tarski @ (k1_relset_1 @ sk_A @ sk_B @ sk_C) @ sk_A)),
% 0.39/0.60      inference('sup-', [status(thm)], ['13', '14'])).
% 0.39/0.60  thf('16', plain,
% 0.39/0.60      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.39/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.60  thf('17', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.39/0.60      inference('demod', [status(thm)], ['15', '16'])).
% 0.39/0.60  thf('18', plain,
% 0.39/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(cc2_relset_1, axiom,
% 0.39/0.60    (![A:$i,B:$i,C:$i]:
% 0.39/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.60       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.39/0.60  thf('19', plain,
% 0.39/0.60      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.39/0.60         ((v5_relat_1 @ X20 @ X22)
% 0.39/0.60          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.39/0.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.39/0.60  thf('20', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.39/0.60      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.60  thf(d19_relat_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( v1_relat_1 @ B ) =>
% 0.39/0.60       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.39/0.60  thf('21', plain,
% 0.39/0.60      (![X5 : $i, X6 : $i]:
% 0.39/0.60         (~ (v5_relat_1 @ X5 @ X6)
% 0.39/0.60          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.39/0.60          | ~ (v1_relat_1 @ X5))),
% 0.39/0.60      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.39/0.60  thf('22', plain,
% 0.39/0.60      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.39/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.39/0.60  thf('23', plain,
% 0.39/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(cc2_relat_1, axiom,
% 0.39/0.60    (![A:$i]:
% 0.39/0.60     ( ( v1_relat_1 @ A ) =>
% 0.39/0.60       ( ![B:$i]:
% 0.39/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.39/0.60  thf('24', plain,
% 0.39/0.60      (![X3 : $i, X4 : $i]:
% 0.39/0.60         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.39/0.60          | (v1_relat_1 @ X3)
% 0.39/0.60          | ~ (v1_relat_1 @ X4))),
% 0.39/0.60      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.39/0.60  thf('25', plain,
% 0.39/0.60      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.39/0.60      inference('sup-', [status(thm)], ['23', '24'])).
% 0.39/0.60  thf(fc6_relat_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.39/0.60  thf('26', plain,
% 0.39/0.60      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.39/0.60      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.39/0.60  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.60      inference('demod', [status(thm)], ['25', '26'])).
% 0.39/0.60  thf('28', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.39/0.60      inference('demod', [status(thm)], ['22', '27'])).
% 0.39/0.60  thf(t79_relat_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( v1_relat_1 @ B ) =>
% 0.39/0.60       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.39/0.60         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.39/0.60  thf('29', plain,
% 0.39/0.60      (![X18 : $i, X19 : $i]:
% 0.39/0.60         (~ (r1_tarski @ (k2_relat_1 @ X18) @ X19)
% 0.39/0.60          | ((k5_relat_1 @ X18 @ (k6_relat_1 @ X19)) = (X18))
% 0.39/0.60          | ~ (v1_relat_1 @ X18))),
% 0.39/0.60      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.39/0.60  thf('30', plain,
% 0.39/0.60      ((~ (v1_relat_1 @ sk_C)
% 0.39/0.60        | ((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (sk_C)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['28', '29'])).
% 0.39/0.60  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.60      inference('demod', [status(thm)], ['25', '26'])).
% 0.39/0.60  thf('32', plain, (((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (sk_C))),
% 0.39/0.60      inference('demod', [status(thm)], ['30', '31'])).
% 0.39/0.60  thf(t71_relat_1, axiom,
% 0.39/0.60    (![A:$i]:
% 0.39/0.60     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.39/0.60       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.39/0.60  thf('33', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 0.39/0.60      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.39/0.60  thf(t182_relat_1, axiom,
% 0.39/0.60    (![A:$i]:
% 0.39/0.60     ( ( v1_relat_1 @ A ) =>
% 0.39/0.60       ( ![B:$i]:
% 0.39/0.60         ( ( v1_relat_1 @ B ) =>
% 0.39/0.60           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.39/0.60             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.39/0.60  thf('34', plain,
% 0.39/0.60      (![X12 : $i, X13 : $i]:
% 0.39/0.60         (~ (v1_relat_1 @ X12)
% 0.39/0.60          | ((k1_relat_1 @ (k5_relat_1 @ X13 @ X12))
% 0.39/0.60              = (k10_relat_1 @ X13 @ (k1_relat_1 @ X12)))
% 0.39/0.60          | ~ (v1_relat_1 @ X13))),
% 0.39/0.60      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.39/0.60  thf(t77_relat_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( v1_relat_1 @ B ) =>
% 0.39/0.60       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.39/0.60         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.39/0.60  thf('35', plain,
% 0.39/0.60      (![X16 : $i, X17 : $i]:
% 0.39/0.60         (~ (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 0.39/0.60          | ((k5_relat_1 @ (k6_relat_1 @ X17) @ X16) = (X16))
% 0.39/0.60          | ~ (v1_relat_1 @ X16))),
% 0.39/0.60      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.39/0.60  thf('36', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.60         (~ (r1_tarski @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ X2)
% 0.39/0.60          | ~ (v1_relat_1 @ X1)
% 0.39/0.60          | ~ (v1_relat_1 @ X0)
% 0.39/0.60          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.39/0.60          | ((k5_relat_1 @ (k6_relat_1 @ X2) @ (k5_relat_1 @ X1 @ X0))
% 0.39/0.60              = (k5_relat_1 @ X1 @ X0)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['34', '35'])).
% 0.39/0.60  thf('37', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.60         (~ (r1_tarski @ (k10_relat_1 @ X2 @ X0) @ X1)
% 0.39/0.60          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 0.39/0.60              (k5_relat_1 @ X2 @ (k6_relat_1 @ X0)))
% 0.39/0.60              = (k5_relat_1 @ X2 @ (k6_relat_1 @ X0)))
% 0.39/0.60          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X0)))
% 0.39/0.60          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.39/0.60          | ~ (v1_relat_1 @ X2))),
% 0.39/0.60      inference('sup-', [status(thm)], ['33', '36'])).
% 0.39/0.60  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.39/0.60  thf('38', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 0.39/0.60      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.39/0.60  thf('39', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.60         (~ (r1_tarski @ (k10_relat_1 @ X2 @ X0) @ X1)
% 0.39/0.60          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 0.39/0.60              (k5_relat_1 @ X2 @ (k6_relat_1 @ X0)))
% 0.39/0.60              = (k5_relat_1 @ X2 @ (k6_relat_1 @ X0)))
% 0.39/0.60          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X0)))
% 0.39/0.60          | ~ (v1_relat_1 @ X2))),
% 0.39/0.60      inference('demod', [status(thm)], ['37', '38'])).
% 0.39/0.60  thf('40', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (~ (v1_relat_1 @ sk_C)
% 0.39/0.60          | ~ (v1_relat_1 @ sk_C)
% 0.39/0.60          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.39/0.60              (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)))
% 0.39/0.60              = (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)))
% 0.39/0.60          | ~ (r1_tarski @ (k10_relat_1 @ sk_C @ sk_B) @ X0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['32', '39'])).
% 0.39/0.60  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.60      inference('demod', [status(thm)], ['25', '26'])).
% 0.39/0.60  thf('42', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.60      inference('demod', [status(thm)], ['25', '26'])).
% 0.39/0.60  thf('43', plain, (((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (sk_C))),
% 0.39/0.60      inference('demod', [status(thm)], ['30', '31'])).
% 0.39/0.60  thf('44', plain, (((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (sk_C))),
% 0.39/0.60      inference('demod', [status(thm)], ['30', '31'])).
% 0.39/0.60  thf('45', plain, (((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (sk_C))),
% 0.39/0.60      inference('demod', [status(thm)], ['30', '31'])).
% 0.39/0.60  thf('46', plain,
% 0.39/0.60      (![X12 : $i, X13 : $i]:
% 0.39/0.60         (~ (v1_relat_1 @ X12)
% 0.39/0.60          | ((k1_relat_1 @ (k5_relat_1 @ X13 @ X12))
% 0.39/0.60              = (k10_relat_1 @ X13 @ (k1_relat_1 @ X12)))
% 0.39/0.60          | ~ (v1_relat_1 @ X13))),
% 0.39/0.60      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.39/0.60  thf('47', plain,
% 0.39/0.60      ((((k1_relat_1 @ sk_C)
% 0.39/0.60          = (k10_relat_1 @ sk_C @ (k1_relat_1 @ (k6_relat_1 @ sk_B))))
% 0.39/0.60        | ~ (v1_relat_1 @ sk_C)
% 0.39/0.60        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['45', '46'])).
% 0.39/0.60  thf('48', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 0.39/0.60      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.39/0.60  thf('49', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.60      inference('demod', [status(thm)], ['25', '26'])).
% 0.39/0.60  thf('50', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 0.39/0.60      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.39/0.60  thf('51', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_B))),
% 0.39/0.60      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 0.39/0.60  thf('52', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (((k5_relat_1 @ (k6_relat_1 @ X0) @ sk_C) = (sk_C))
% 0.39/0.60          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.39/0.60      inference('demod', [status(thm)], ['40', '41', '42', '43', '44', '51'])).
% 0.39/0.60  thf('53', plain, (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C) = (sk_C))),
% 0.39/0.60      inference('sup-', [status(thm)], ['17', '52'])).
% 0.39/0.60  thf(t160_relat_1, axiom,
% 0.39/0.60    (![A:$i]:
% 0.39/0.60     ( ( v1_relat_1 @ A ) =>
% 0.39/0.60       ( ![B:$i]:
% 0.39/0.60         ( ( v1_relat_1 @ B ) =>
% 0.39/0.60           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.39/0.60             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.39/0.60  thf('54', plain,
% 0.39/0.60      (![X10 : $i, X11 : $i]:
% 0.39/0.60         (~ (v1_relat_1 @ X10)
% 0.39/0.60          | ((k2_relat_1 @ (k5_relat_1 @ X11 @ X10))
% 0.39/0.60              = (k9_relat_1 @ X10 @ (k2_relat_1 @ X11)))
% 0.39/0.60          | ~ (v1_relat_1 @ X11))),
% 0.39/0.60      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.39/0.60  thf('55', plain,
% 0.39/0.60      ((((k2_relat_1 @ sk_C)
% 0.39/0.60          = (k9_relat_1 @ sk_C @ (k2_relat_1 @ (k6_relat_1 @ sk_A))))
% 0.39/0.60        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 0.39/0.60        | ~ (v1_relat_1 @ sk_C))),
% 0.39/0.60      inference('sup+', [status(thm)], ['53', '54'])).
% 0.39/0.60  thf('56', plain, (![X15 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 0.39/0.60      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.39/0.60  thf('57', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 0.39/0.60      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.39/0.60  thf('58', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.60      inference('demod', [status(thm)], ['25', '26'])).
% 0.39/0.60  thf('59', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.39/0.60      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 0.39/0.60  thf('60', plain,
% 0.39/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(redefinition_k2_relset_1, axiom,
% 0.39/0.60    (![A:$i,B:$i,C:$i]:
% 0.39/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.60       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.39/0.60  thf('61', plain,
% 0.39/0.60      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.39/0.60         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 0.39/0.60          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.39/0.60      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.39/0.60  thf('62', plain,
% 0.39/0.60      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.39/0.60      inference('sup-', [status(thm)], ['60', '61'])).
% 0.39/0.60  thf('63', plain,
% 0.39/0.60      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.39/0.60         <= (~
% 0.39/0.60             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.39/0.60                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.39/0.60      inference('demod', [status(thm)], ['10', '59', '62'])).
% 0.39/0.60  thf('64', plain,
% 0.39/0.60      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.39/0.60          = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.60      inference('simplify', [status(thm)], ['63'])).
% 0.39/0.60  thf('65', plain,
% 0.39/0.60      (~
% 0.39/0.60       (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.39/0.60          = (k1_relset_1 @ sk_A @ sk_B @ sk_C))) | 
% 0.39/0.60       ~
% 0.39/0.60       (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.39/0.60          = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.60      inference('split', [status(esa)], ['0'])).
% 0.39/0.60  thf('66', plain,
% 0.39/0.60      (~
% 0.39/0.60       (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.39/0.60          = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.60      inference('sat_resolution*', [status(thm)], ['64', '65'])).
% 0.39/0.60  thf('67', plain,
% 0.39/0.60      (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B) != (k1_relat_1 @ sk_C))),
% 0.39/0.60      inference('simpl_trail', [status(thm)], ['5', '66'])).
% 0.39/0.60  thf('68', plain,
% 0.39/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(redefinition_k8_relset_1, axiom,
% 0.39/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.60       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.39/0.60  thf('69', plain,
% 0.39/0.60      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.39/0.60         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.39/0.60          | ((k8_relset_1 @ X37 @ X38 @ X36 @ X39) = (k10_relat_1 @ X36 @ X39)))),
% 0.39/0.60      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.39/0.60  thf('70', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['68', '69'])).
% 0.39/0.60  thf('71', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_B))),
% 0.39/0.60      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 0.39/0.60  thf('72', plain, (((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))),
% 0.39/0.60      inference('demod', [status(thm)], ['67', '70', '71'])).
% 0.39/0.60  thf('73', plain, ($false), inference('simplify', [status(thm)], ['72'])).
% 0.39/0.60  
% 0.39/0.60  % SZS output end Refutation
% 0.39/0.60  
% 0.39/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
