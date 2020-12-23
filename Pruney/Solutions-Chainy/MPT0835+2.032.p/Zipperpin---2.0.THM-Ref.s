%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gxUcPzgn1B

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:49 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 209 expanded)
%              Number of leaves         :   38 (  76 expanded)
%              Depth                    :   17
%              Number of atoms          : 1020 (2630 expanded)
%              Number of equality atoms :   79 ( 165 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

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

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ( ( k7_relat_1 @ X20 @ X21 )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) )
        = ( k9_relat_1 @ X10 @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

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

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('8',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( ( k8_relset_1 @ X36 @ X37 @ X35 @ X38 )
        = ( k10_relat_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v5_relat_1 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('15',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('22',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['17','22'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('24',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X18 ) @ X19 )
      | ( ( k5_relat_1 @ X18 @ ( k6_relat_1 @ X19 ) )
        = X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_A ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('27',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_A ) )
    = sk_C ),
    inference(demod,[status(thm)],['25','26'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('28',plain,(
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

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) )
        = ( k10_relat_1 @ X13 @ ( k1_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('31',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['27','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('35',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('37',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k7_relset_1 @ X32 @ X33 @ X31 @ X34 )
        = ( k9_relat_1 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('40',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('41',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['12','35','38','41'])).

thf('43',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('44',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X18 ) @ X19 )
      | ( ( k5_relat_1 @ X18 @ ( k6_relat_1 @ X19 ) )
        = X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('51',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['10'])).

thf('52',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('55',plain,(
    v4_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['53','54'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('56',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14
        = ( k7_relat_1 @ X14 @ X15 ) )
      | ~ ( v4_relat_1 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('57',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('59',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) )
        = ( k9_relat_1 @ X10 @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('61',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('63',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('65',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('66',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k2_relat_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['52','63','66'])).

thf('68',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['49','67'])).

thf('69',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
       != ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['48','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('71',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    = ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['10'])).

thf('74',plain,(
    ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
 != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['72','73'])).

thf('75',plain,(
    ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['42','74'])).

thf('76',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('78',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    $false ),
    inference(simplify,[status(thm)],['78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gxUcPzgn1B
% 0.13/0.32  % Computer   : n006.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 15:27:22 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  % Running portfolio for 600 s
% 0.13/0.32  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.32  % Number of cores: 8
% 0.13/0.33  % Python version: Python 3.6.8
% 0.13/0.33  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 79 iterations in 0.046s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.48  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.48  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.19/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.48  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.19/0.48  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.19/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.48  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.19/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.48  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.19/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.19/0.48  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.48  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.19/0.48  thf(d10_xboole_0, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.48  thf('0', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.48  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.19/0.48      inference('simplify', [status(thm)], ['0'])).
% 0.19/0.48  thf(t97_relat_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ B ) =>
% 0.19/0.48       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.19/0.48         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      (![X20 : $i, X21 : $i]:
% 0.19/0.48         (~ (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 0.19/0.48          | ((k7_relat_1 @ X20 @ X21) = (X20))
% 0.19/0.48          | ~ (v1_relat_1 @ X20))),
% 0.19/0.48      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.48  thf(t148_relat_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ B ) =>
% 0.19/0.48       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      (![X10 : $i, X11 : $i]:
% 0.19/0.48         (((k2_relat_1 @ (k7_relat_1 @ X10 @ X11)) = (k9_relat_1 @ X10 @ X11))
% 0.19/0.48          | ~ (v1_relat_1 @ X10))),
% 0.19/0.48      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.19/0.48  thf('5', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.19/0.48          | ~ (v1_relat_1 @ X0)
% 0.19/0.48          | ~ (v1_relat_1 @ X0))),
% 0.19/0.48      inference('sup+', [status(thm)], ['3', '4'])).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (v1_relat_1 @ X0)
% 0.19/0.48          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.19/0.48      inference('simplify', [status(thm)], ['5'])).
% 0.19/0.48  thf(t39_relset_1, conjecture,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.19/0.48       ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.19/0.48           ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.19/0.48         ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.19/0.48           ( k1_relset_1 @ B @ A @ C ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.48        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.19/0.48          ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.19/0.48              ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.19/0.48            ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.19/0.48              ( k1_relset_1 @ B @ A @ C ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t39_relset_1])).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(redefinition_k8_relset_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.48       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.19/0.48  thf('8', plain,
% 0.19/0.48      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.19/0.48          | ((k8_relset_1 @ X36 @ X37 @ X35 @ X38) = (k10_relat_1 @ X35 @ X38)))),
% 0.19/0.48      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.19/0.48          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.19/0.48          != (k2_relset_1 @ sk_B @ sk_A @ sk_C))
% 0.19/0.48        | ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.19/0.48            (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.19/0.48            != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.19/0.48          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.19/0.48          != (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.19/0.48         <= (~
% 0.19/0.48             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.19/0.48                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.19/0.48                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.19/0.48      inference('split', [status(esa)], ['10'])).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ (k10_relat_1 @ sk_C @ sk_A))
% 0.19/0.48          != (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.19/0.48         <= (~
% 0.19/0.48             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.19/0.48                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.19/0.48                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['9', '11'])).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(cc2_relset_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.48       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.19/0.48         ((v5_relat_1 @ X22 @ X24)
% 0.19/0.48          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.19/0.48      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.48  thf('15', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.19/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.48  thf(d19_relat_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ B ) =>
% 0.19/0.48       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      (![X5 : $i, X6 : $i]:
% 0.19/0.48         (~ (v5_relat_1 @ X5 @ X6)
% 0.19/0.48          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.19/0.48          | ~ (v1_relat_1 @ X5))),
% 0.19/0.48      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(cc2_relat_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ A ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      (![X3 : $i, X4 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.19/0.48          | (v1_relat_1 @ X3)
% 0.19/0.48          | ~ (v1_relat_1 @ X4))),
% 0.19/0.48      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.19/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.48  thf(fc6_relat_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.19/0.48  thf('21', plain,
% 0.19/0.48      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.19/0.48      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.19/0.48  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.48  thf('23', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)),
% 0.19/0.48      inference('demod', [status(thm)], ['17', '22'])).
% 0.19/0.48  thf(t79_relat_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ B ) =>
% 0.19/0.48       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.19/0.48         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.19/0.48  thf('24', plain,
% 0.19/0.48      (![X18 : $i, X19 : $i]:
% 0.19/0.48         (~ (r1_tarski @ (k2_relat_1 @ X18) @ X19)
% 0.19/0.48          | ((k5_relat_1 @ X18 @ (k6_relat_1 @ X19)) = (X18))
% 0.19/0.48          | ~ (v1_relat_1 @ X18))),
% 0.19/0.48      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.19/0.48  thf('25', plain,
% 0.19/0.48      ((~ (v1_relat_1 @ sk_C)
% 0.19/0.48        | ((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_A)) = (sk_C)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.48  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.48  thf('27', plain, (((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_A)) = (sk_C))),
% 0.19/0.48      inference('demod', [status(thm)], ['25', '26'])).
% 0.19/0.48  thf(t71_relat_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.19/0.48       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.19/0.48  thf('28', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 0.19/0.48      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.48  thf(t182_relat_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ A ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( v1_relat_1 @ B ) =>
% 0.19/0.48           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.19/0.48             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.19/0.48  thf('29', plain,
% 0.19/0.48      (![X12 : $i, X13 : $i]:
% 0.19/0.48         (~ (v1_relat_1 @ X12)
% 0.19/0.48          | ((k1_relat_1 @ (k5_relat_1 @ X13 @ X12))
% 0.19/0.48              = (k10_relat_1 @ X13 @ (k1_relat_1 @ X12)))
% 0.19/0.48          | ~ (v1_relat_1 @ X13))),
% 0.19/0.48      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.19/0.48  thf('30', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.19/0.48            = (k10_relat_1 @ X1 @ X0))
% 0.19/0.48          | ~ (v1_relat_1 @ X1)
% 0.19/0.48          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.19/0.48      inference('sup+', [status(thm)], ['28', '29'])).
% 0.19/0.48  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.19/0.48  thf('31', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.19/0.48  thf('32', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.19/0.48            = (k10_relat_1 @ X1 @ X0))
% 0.19/0.48          | ~ (v1_relat_1 @ X1))),
% 0.19/0.48      inference('demod', [status(thm)], ['30', '31'])).
% 0.19/0.48  thf('33', plain,
% 0.19/0.48      ((((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_A))
% 0.19/0.48        | ~ (v1_relat_1 @ sk_C))),
% 0.19/0.48      inference('sup+', [status(thm)], ['27', '32'])).
% 0.19/0.48  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.48  thf('35', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_A))),
% 0.19/0.48      inference('demod', [status(thm)], ['33', '34'])).
% 0.19/0.48  thf('36', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(redefinition_k7_relset_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.48       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.19/0.48  thf('37', plain,
% 0.19/0.48      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.19/0.48          | ((k7_relset_1 @ X32 @ X33 @ X31 @ X34) = (k9_relat_1 @ X31 @ X34)))),
% 0.19/0.48      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.19/0.48  thf('38', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['36', '37'])).
% 0.19/0.48  thf('39', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(redefinition_k2_relset_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.48       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.19/0.48  thf('40', plain,
% 0.19/0.48      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.19/0.48         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 0.19/0.48          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.19/0.48      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.19/0.48  thf('41', plain,
% 0.19/0.48      (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.19/0.48      inference('sup-', [status(thm)], ['39', '40'])).
% 0.19/0.48  thf('42', plain,
% 0.19/0.48      ((((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.19/0.48         <= (~
% 0.19/0.48             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.19/0.48                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.19/0.48                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.19/0.48      inference('demod', [status(thm)], ['12', '35', '38', '41'])).
% 0.19/0.48  thf('43', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.19/0.48      inference('simplify', [status(thm)], ['0'])).
% 0.19/0.48  thf('44', plain,
% 0.19/0.48      (![X18 : $i, X19 : $i]:
% 0.19/0.48         (~ (r1_tarski @ (k2_relat_1 @ X18) @ X19)
% 0.19/0.48          | ((k5_relat_1 @ X18 @ (k6_relat_1 @ X19)) = (X18))
% 0.19/0.48          | ~ (v1_relat_1 @ X18))),
% 0.19/0.48      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.19/0.48  thf('45', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (v1_relat_1 @ X0)
% 0.19/0.48          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))) = (X0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['43', '44'])).
% 0.19/0.48  thf('46', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.19/0.48            = (k10_relat_1 @ X1 @ X0))
% 0.19/0.48          | ~ (v1_relat_1 @ X1))),
% 0.19/0.48      inference('demod', [status(thm)], ['30', '31'])).
% 0.19/0.48  thf('47', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.19/0.48          | ~ (v1_relat_1 @ X0)
% 0.19/0.48          | ~ (v1_relat_1 @ X0))),
% 0.19/0.48      inference('sup+', [status(thm)], ['45', '46'])).
% 0.19/0.48  thf('48', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (v1_relat_1 @ X0)
% 0.19/0.48          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 0.19/0.48      inference('simplify', [status(thm)], ['47'])).
% 0.19/0.48  thf('49', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.48  thf('50', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['36', '37'])).
% 0.19/0.48  thf('51', plain,
% 0.19/0.48      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.19/0.48          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.19/0.48          != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.19/0.48         <= (~
% 0.19/0.48             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.19/0.48                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.19/0.48                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.19/0.48      inference('split', [status(esa)], ['10'])).
% 0.19/0.48  thf('52', plain,
% 0.19/0.48      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ (k9_relat_1 @ sk_C @ sk_B))
% 0.19/0.48          != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.19/0.48         <= (~
% 0.19/0.48             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.19/0.48                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.19/0.48                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['50', '51'])).
% 0.19/0.48  thf('53', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('54', plain,
% 0.19/0.48      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.19/0.48         ((v4_relat_1 @ X22 @ X23)
% 0.19/0.48          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.19/0.48      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.48  thf('55', plain, ((v4_relat_1 @ sk_C @ sk_B)),
% 0.19/0.48      inference('sup-', [status(thm)], ['53', '54'])).
% 0.19/0.48  thf(t209_relat_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.19/0.48       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.19/0.48  thf('56', plain,
% 0.19/0.48      (![X14 : $i, X15 : $i]:
% 0.19/0.48         (((X14) = (k7_relat_1 @ X14 @ X15))
% 0.19/0.48          | ~ (v4_relat_1 @ X14 @ X15)
% 0.19/0.48          | ~ (v1_relat_1 @ X14))),
% 0.19/0.48      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.19/0.48  thf('57', plain,
% 0.19/0.48      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_B)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['55', '56'])).
% 0.19/0.48  thf('58', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.48  thf('59', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.19/0.48      inference('demod', [status(thm)], ['57', '58'])).
% 0.19/0.48  thf('60', plain,
% 0.19/0.48      (![X10 : $i, X11 : $i]:
% 0.19/0.48         (((k2_relat_1 @ (k7_relat_1 @ X10 @ X11)) = (k9_relat_1 @ X10 @ X11))
% 0.19/0.48          | ~ (v1_relat_1 @ X10))),
% 0.19/0.48      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.19/0.48  thf('61', plain,
% 0.19/0.48      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))
% 0.19/0.48        | ~ (v1_relat_1 @ sk_C))),
% 0.19/0.48      inference('sup+', [status(thm)], ['59', '60'])).
% 0.19/0.48  thf('62', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.48  thf('63', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))),
% 0.19/0.48      inference('demod', [status(thm)], ['61', '62'])).
% 0.19/0.48  thf('64', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(redefinition_k1_relset_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.48       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.19/0.48  thf('65', plain,
% 0.19/0.48      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.19/0.48         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 0.19/0.48          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.19/0.48      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.19/0.48  thf('66', plain,
% 0.19/0.48      (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.19/0.48      inference('sup-', [status(thm)], ['64', '65'])).
% 0.19/0.48  thf('67', plain,
% 0.19/0.48      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ (k2_relat_1 @ sk_C))
% 0.19/0.48          != (k1_relat_1 @ sk_C)))
% 0.19/0.48         <= (~
% 0.19/0.48             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.19/0.48                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.19/0.48                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.19/0.48      inference('demod', [status(thm)], ['52', '63', '66'])).
% 0.19/0.48  thf('68', plain,
% 0.19/0.48      ((((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 0.19/0.48         <= (~
% 0.19/0.48             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.19/0.48                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.19/0.48                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['49', '67'])).
% 0.19/0.48  thf('69', plain,
% 0.19/0.48      (((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)) | ~ (v1_relat_1 @ sk_C)))
% 0.19/0.48         <= (~
% 0.19/0.48             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.19/0.48                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.19/0.48                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['48', '68'])).
% 0.19/0.48  thf('70', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.48  thf('71', plain,
% 0.19/0.48      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 0.19/0.48         <= (~
% 0.19/0.48             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.19/0.48                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.19/0.48                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.19/0.48      inference('demod', [status(thm)], ['69', '70'])).
% 0.19/0.48  thf('72', plain,
% 0.19/0.48      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.19/0.48          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.19/0.48          = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['71'])).
% 0.19/0.48  thf('73', plain,
% 0.19/0.48      (~
% 0.19/0.48       (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.19/0.48          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.19/0.48          = (k2_relset_1 @ sk_B @ sk_A @ sk_C))) | 
% 0.19/0.48       ~
% 0.19/0.48       (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.19/0.48          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.19/0.48          = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.19/0.48      inference('split', [status(esa)], ['10'])).
% 0.19/0.48  thf('74', plain,
% 0.19/0.48      (~
% 0.19/0.48       (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.19/0.48          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.19/0.48          = (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.19/0.48      inference('sat_resolution*', [status(thm)], ['72', '73'])).
% 0.19/0.48  thf('75', plain,
% 0.19/0.48      (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['42', '74'])).
% 0.19/0.48  thf('76', plain,
% 0.19/0.48      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)) | ~ (v1_relat_1 @ sk_C))),
% 0.19/0.48      inference('sup-', [status(thm)], ['6', '75'])).
% 0.19/0.48  thf('77', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.48  thf('78', plain, (((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))),
% 0.19/0.48      inference('demod', [status(thm)], ['76', '77'])).
% 0.19/0.48  thf('79', plain, ($false), inference('simplify', [status(thm)], ['78'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
