%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.snkGSZoR53

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:48 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 338 expanded)
%              Number of leaves         :   38 ( 117 expanded)
%              Depth                    :   17
%              Number of atoms          : 1127 (4212 expanded)
%              Number of equality atoms :   83 ( 239 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t39_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) )
          = ( k2_relset_1 @ B @ A @ C ) )
        & ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) )
          = ( k1_relset_1 @ B @ A @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
       => ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) )
            = ( k2_relset_1 @ B @ A @ C ) )
          & ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) )
            = ( k1_relset_1 @ B @ A @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_relset_1])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('3',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X37 ) @ X38 )
      | ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('7',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14
        = ( k7_relat_1 @ X14 @ X15 ) )
      | ~ ( v4_relat_1 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('14',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) )
        = ( k9_relat_1 @ X10 @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('17',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['12','13'])).

thf('19',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('21',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k8_relset_1 @ X34 @ X35 @ X33 @ X36 )
        = ( k10_relat_1 @ X33 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v5_relat_1 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('28',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['26','27'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('29',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['12','13'])).

thf('32',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['30','31'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('33',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X18 ) @ X19 )
      | ( ( k5_relat_1 @ X18 @ ( k6_relat_1 @ X19 ) )
        = X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_A ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['12','13'])).

thf('36',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_A ) )
    = sk_C ),
    inference(demod,[status(thm)],['34','35'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('37',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) )
        = ( k10_relat_1 @ X13 @ ( k1_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('40',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['12','13'])).

thf('44',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('46',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( ( k7_relset_1 @ X30 @ X31 @ X29 @ X32 )
        = ( k9_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('49',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('50',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['25','44','47','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('54',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['23'])).

thf('55',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('58',plain,(
    v4_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14
        = ( k7_relat_1 @ X14 @ X15 ) )
      | ~ ( v4_relat_1 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('60',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['12','13'])).

thf('62',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) )
        = ( k9_relat_1 @ X10 @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('64',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['12','13'])).

thf('66',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('68',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('69',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k2_relat_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['55','66','69'])).

thf('71',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','70'])).

thf('72',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('73',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('74',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) )
        = ( k9_relat_1 @ X10 @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('75',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X18 ) @ X19 )
      | ( ( k5_relat_1 @ X18 @ ( k6_relat_1 @ X19 ) )
        = X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k6_relat_1 @ X2 ) )
        = ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ X0 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ ( k6_relat_1 @ X0 ) )
        = ( k7_relat_1 @ sk_C @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('79',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('80',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('81',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['12','13'])).

thf('82',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['12','13'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ X0 ) )
        = sk_C ) ) ),
    inference(demod,[status(thm)],['77','78','79','80','81','82'])).

thf('84',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    = sk_C ),
    inference('sup-',[status(thm)],['72','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('86',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['12','13'])).

thf('88',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['71','88'])).

thf('90',plain,
    ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    = ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['23'])).

thf('92',plain,(
    ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
 != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['90','91'])).

thf('93',plain,(
    ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['51','92'])).

thf('94',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['19','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.snkGSZoR53
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:10:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 98 iterations in 0.053s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.52  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.52  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.52  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.52  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.52  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.52  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.22/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.52  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.52  thf(d10_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.52  thf('0', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.52  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.52      inference('simplify', [status(thm)], ['0'])).
% 0.22/0.52  thf(t39_relset_1, conjecture,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.22/0.52       ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.22/0.52           ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.22/0.52         ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.22/0.52           ( k1_relset_1 @ B @ A @ C ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.52        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.22/0.52          ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.22/0.52              ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.22/0.52            ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.22/0.52              ( k1_relset_1 @ B @ A @ C ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t39_relset_1])).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t13_relset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.22/0.52       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 0.22/0.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.22/0.52         (~ (r1_tarski @ (k1_relat_1 @ X37) @ X38)
% 0.22/0.52          | (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.22/0.52          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39))))),
% 0.22/0.52      inference('cnf', [status(esa)], [t13_relset_1])).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A)))
% 0.22/0.52          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_C @ 
% 0.22/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['1', '4'])).
% 0.22/0.52  thf(cc2_relset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.52       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.52         ((v4_relat_1 @ X20 @ X21)
% 0.22/0.52          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.52  thf('7', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.22/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.52  thf(t209_relat_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.22/0.52       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (![X14 : $i, X15 : $i]:
% 0.22/0.52         (((X14) = (k7_relat_1 @ X14 @ X15))
% 0.22/0.52          | ~ (v4_relat_1 @ X14 @ X15)
% 0.22/0.52          | ~ (v1_relat_1 @ X14))),
% 0.22/0.52      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      ((~ (v1_relat_1 @ sk_C)
% 0.22/0.52        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(cc2_relat_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (![X3 : $i, X4 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.22/0.52          | (v1_relat_1 @ X3)
% 0.22/0.52          | ~ (v1_relat_1 @ X4))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.22/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.52  thf(fc6_relat_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.22/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.52  thf('14', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.52      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.52  thf('15', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.22/0.52      inference('demod', [status(thm)], ['9', '14'])).
% 0.22/0.52  thf(t148_relat_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ B ) =>
% 0.22/0.52       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (![X10 : $i, X11 : $i]:
% 0.22/0.52         (((k2_relat_1 @ (k7_relat_1 @ X10 @ X11)) = (k9_relat_1 @ X10 @ X11))
% 0.22/0.52          | ~ (v1_relat_1 @ X10))),
% 0.22/0.52      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 0.22/0.52        | ~ (v1_relat_1 @ sk_C))),
% 0.22/0.52      inference('sup+', [status(thm)], ['15', '16'])).
% 0.22/0.52  thf('18', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.52      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.22/0.52      inference('demod', [status(thm)], ['17', '18'])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(redefinition_k8_relset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.52       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.22/0.52          | ((k8_relset_1 @ X34 @ X35 @ X33 @ X36) = (k10_relat_1 @ X33 @ X36)))),
% 0.22/0.52      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.52          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.22/0.52          != (k2_relset_1 @ sk_B @ sk_A @ sk_C))
% 0.22/0.52        | ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.52            (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.22/0.52            != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.52          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.22/0.52          != (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.22/0.52         <= (~
% 0.22/0.52             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.52                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.22/0.52                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.22/0.52      inference('split', [status(esa)], ['23'])).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ (k10_relat_1 @ sk_C @ sk_A))
% 0.22/0.52          != (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.22/0.52         <= (~
% 0.22/0.52             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.52                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.22/0.52                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['22', '24'])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.52         ((v5_relat_1 @ X20 @ X22)
% 0.22/0.52          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.52  thf('28', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.22/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.52  thf(d19_relat_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ B ) =>
% 0.22/0.52       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      (![X5 : $i, X6 : $i]:
% 0.22/0.52         (~ (v5_relat_1 @ X5 @ X6)
% 0.22/0.52          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.22/0.52          | ~ (v1_relat_1 @ X5))),
% 0.22/0.52      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.52  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.52      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.52  thf('32', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)),
% 0.22/0.52      inference('demod', [status(thm)], ['30', '31'])).
% 0.22/0.52  thf(t79_relat_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ B ) =>
% 0.22/0.52       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.22/0.52         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.22/0.52  thf('33', plain,
% 0.22/0.52      (![X18 : $i, X19 : $i]:
% 0.22/0.52         (~ (r1_tarski @ (k2_relat_1 @ X18) @ X19)
% 0.22/0.52          | ((k5_relat_1 @ X18 @ (k6_relat_1 @ X19)) = (X18))
% 0.22/0.52          | ~ (v1_relat_1 @ X18))),
% 0.22/0.52      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      ((~ (v1_relat_1 @ sk_C)
% 0.22/0.52        | ((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_A)) = (sk_C)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.52  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.52      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.52  thf('36', plain, (((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_A)) = (sk_C))),
% 0.22/0.52      inference('demod', [status(thm)], ['34', '35'])).
% 0.22/0.52  thf(t71_relat_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.22/0.52       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.52  thf('37', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 0.22/0.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.52  thf(t182_relat_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( v1_relat_1 @ B ) =>
% 0.22/0.52           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.22/0.52             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.22/0.52  thf('38', plain,
% 0.22/0.52      (![X12 : $i, X13 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ X12)
% 0.22/0.52          | ((k1_relat_1 @ (k5_relat_1 @ X13 @ X12))
% 0.22/0.52              = (k10_relat_1 @ X13 @ (k1_relat_1 @ X12)))
% 0.22/0.52          | ~ (v1_relat_1 @ X13))),
% 0.22/0.52      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.22/0.52  thf('39', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.22/0.52            = (k10_relat_1 @ X1 @ X0))
% 0.22/0.52          | ~ (v1_relat_1 @ X1)
% 0.22/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['37', '38'])).
% 0.22/0.52  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.22/0.52  thf('40', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.52  thf('41', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.22/0.52            = (k10_relat_1 @ X1 @ X0))
% 0.22/0.52          | ~ (v1_relat_1 @ X1))),
% 0.22/0.52      inference('demod', [status(thm)], ['39', '40'])).
% 0.22/0.52  thf('42', plain,
% 0.22/0.52      ((((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_A))
% 0.22/0.52        | ~ (v1_relat_1 @ sk_C))),
% 0.22/0.52      inference('sup+', [status(thm)], ['36', '41'])).
% 0.22/0.52  thf('43', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.52      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.52  thf('44', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['42', '43'])).
% 0.22/0.52  thf('45', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(redefinition_k7_relset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.52       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.22/0.52  thf('46', plain,
% 0.22/0.52      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.22/0.52          | ((k7_relset_1 @ X30 @ X31 @ X29 @ X32) = (k9_relat_1 @ X29 @ X32)))),
% 0.22/0.52      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.22/0.52  thf('47', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['45', '46'])).
% 0.22/0.52  thf('48', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(redefinition_k2_relset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.52       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.22/0.52  thf('49', plain,
% 0.22/0.52      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.22/0.52         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 0.22/0.52          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.22/0.52      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.22/0.52  thf('50', plain,
% 0.22/0.52      (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.22/0.52      inference('sup-', [status(thm)], ['48', '49'])).
% 0.22/0.52  thf('51', plain,
% 0.22/0.52      ((((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.22/0.52         <= (~
% 0.22/0.52             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.52                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.22/0.52                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.22/0.52      inference('demod', [status(thm)], ['25', '44', '47', '50'])).
% 0.22/0.52  thf('52', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.52  thf('53', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['45', '46'])).
% 0.22/0.52  thf('54', plain,
% 0.22/0.52      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.52          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.22/0.52          != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.22/0.52         <= (~
% 0.22/0.52             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.52                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.22/0.52                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.22/0.52      inference('split', [status(esa)], ['23'])).
% 0.22/0.52  thf('55', plain,
% 0.22/0.52      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ (k9_relat_1 @ sk_C @ sk_B))
% 0.22/0.52          != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.22/0.52         <= (~
% 0.22/0.52             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.52                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.22/0.52                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['53', '54'])).
% 0.22/0.52  thf('56', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('57', plain,
% 0.22/0.52      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.52         ((v4_relat_1 @ X20 @ X21)
% 0.22/0.52          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.52  thf('58', plain, ((v4_relat_1 @ sk_C @ sk_B)),
% 0.22/0.52      inference('sup-', [status(thm)], ['56', '57'])).
% 0.22/0.52  thf('59', plain,
% 0.22/0.52      (![X14 : $i, X15 : $i]:
% 0.22/0.52         (((X14) = (k7_relat_1 @ X14 @ X15))
% 0.22/0.52          | ~ (v4_relat_1 @ X14 @ X15)
% 0.22/0.52          | ~ (v1_relat_1 @ X14))),
% 0.22/0.52      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.22/0.52  thf('60', plain,
% 0.22/0.52      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_B)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['58', '59'])).
% 0.22/0.52  thf('61', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.52      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.52  thf('62', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['60', '61'])).
% 0.22/0.52  thf('63', plain,
% 0.22/0.52      (![X10 : $i, X11 : $i]:
% 0.22/0.52         (((k2_relat_1 @ (k7_relat_1 @ X10 @ X11)) = (k9_relat_1 @ X10 @ X11))
% 0.22/0.52          | ~ (v1_relat_1 @ X10))),
% 0.22/0.52      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.22/0.52  thf('64', plain,
% 0.22/0.52      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))
% 0.22/0.52        | ~ (v1_relat_1 @ sk_C))),
% 0.22/0.52      inference('sup+', [status(thm)], ['62', '63'])).
% 0.22/0.52  thf('65', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.52      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.52  thf('66', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['64', '65'])).
% 0.22/0.52  thf('67', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(redefinition_k1_relset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.52       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.22/0.52  thf('68', plain,
% 0.22/0.52      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.22/0.52         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 0.22/0.52          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.22/0.52      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.22/0.52  thf('69', plain,
% 0.22/0.52      (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.22/0.52      inference('sup-', [status(thm)], ['67', '68'])).
% 0.22/0.52  thf('70', plain,
% 0.22/0.52      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ (k2_relat_1 @ sk_C))
% 0.22/0.52          != (k1_relat_1 @ sk_C)))
% 0.22/0.52         <= (~
% 0.22/0.52             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.52                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.22/0.52                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.22/0.52      inference('demod', [status(thm)], ['55', '66', '69'])).
% 0.22/0.52  thf('71', plain,
% 0.22/0.52      ((((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 0.22/0.52         <= (~
% 0.22/0.52             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.52                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.22/0.52                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['52', '70'])).
% 0.22/0.52  thf('72', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.52      inference('simplify', [status(thm)], ['0'])).
% 0.22/0.52  thf('73', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['64', '65'])).
% 0.22/0.52  thf('74', plain,
% 0.22/0.52      (![X10 : $i, X11 : $i]:
% 0.22/0.52         (((k2_relat_1 @ (k7_relat_1 @ X10 @ X11)) = (k9_relat_1 @ X10 @ X11))
% 0.22/0.52          | ~ (v1_relat_1 @ X10))),
% 0.22/0.52      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.22/0.52  thf('75', plain,
% 0.22/0.52      (![X18 : $i, X19 : $i]:
% 0.22/0.52         (~ (r1_tarski @ (k2_relat_1 @ X18) @ X19)
% 0.22/0.52          | ((k5_relat_1 @ X18 @ (k6_relat_1 @ X19)) = (X18))
% 0.22/0.52          | ~ (v1_relat_1 @ X18))),
% 0.22/0.52      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.22/0.52  thf('76', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.52         (~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 0.22/0.52          | ~ (v1_relat_1 @ X1)
% 0.22/0.52          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.22/0.52          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k6_relat_1 @ X2))
% 0.22/0.52              = (k7_relat_1 @ X1 @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['74', '75'])).
% 0.22/0.52  thf('77', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (r1_tarski @ (k2_relat_1 @ sk_C) @ X0)
% 0.22/0.52          | ((k5_relat_1 @ (k7_relat_1 @ sk_C @ sk_B) @ (k6_relat_1 @ X0))
% 0.22/0.52              = (k7_relat_1 @ sk_C @ sk_B))
% 0.22/0.52          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_B))
% 0.22/0.52          | ~ (v1_relat_1 @ sk_C))),
% 0.22/0.52      inference('sup-', [status(thm)], ['73', '76'])).
% 0.22/0.52  thf('78', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['60', '61'])).
% 0.22/0.52  thf('79', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['60', '61'])).
% 0.22/0.52  thf('80', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['60', '61'])).
% 0.22/0.52  thf('81', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.52      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.52  thf('82', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.52      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.52  thf('83', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (r1_tarski @ (k2_relat_1 @ sk_C) @ X0)
% 0.22/0.52          | ((k5_relat_1 @ sk_C @ (k6_relat_1 @ X0)) = (sk_C)))),
% 0.22/0.52      inference('demod', [status(thm)], ['77', '78', '79', '80', '81', '82'])).
% 0.22/0.52  thf('84', plain,
% 0.22/0.52      (((k5_relat_1 @ sk_C @ (k6_relat_1 @ (k2_relat_1 @ sk_C))) = (sk_C))),
% 0.22/0.52      inference('sup-', [status(thm)], ['72', '83'])).
% 0.22/0.52  thf('85', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.22/0.52            = (k10_relat_1 @ X1 @ X0))
% 0.22/0.52          | ~ (v1_relat_1 @ X1))),
% 0.22/0.52      inference('demod', [status(thm)], ['39', '40'])).
% 0.22/0.52  thf('86', plain,
% 0.22/0.52      ((((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.22/0.52        | ~ (v1_relat_1 @ sk_C))),
% 0.22/0.52      inference('sup+', [status(thm)], ['84', '85'])).
% 0.22/0.52  thf('87', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.52      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.52  thf('88', plain,
% 0.22/0.52      (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 0.22/0.52      inference('demod', [status(thm)], ['86', '87'])).
% 0.22/0.52  thf('89', plain,
% 0.22/0.52      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 0.22/0.52         <= (~
% 0.22/0.52             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.52                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.22/0.52                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.22/0.52      inference('demod', [status(thm)], ['71', '88'])).
% 0.22/0.52  thf('90', plain,
% 0.22/0.52      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.52          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.22/0.52          = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['89'])).
% 0.22/0.52  thf('91', plain,
% 0.22/0.52      (~
% 0.22/0.52       (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.52          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.22/0.52          = (k2_relset_1 @ sk_B @ sk_A @ sk_C))) | 
% 0.22/0.52       ~
% 0.22/0.52       (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.52          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.22/0.52          = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.22/0.52      inference('split', [status(esa)], ['23'])).
% 0.22/0.52  thf('92', plain,
% 0.22/0.52      (~
% 0.22/0.52       (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.22/0.52          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.22/0.52          = (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['90', '91'])).
% 0.22/0.52  thf('93', plain,
% 0.22/0.52      (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['51', '92'])).
% 0.22/0.52  thf('94', plain, ($false),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['19', '93'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
