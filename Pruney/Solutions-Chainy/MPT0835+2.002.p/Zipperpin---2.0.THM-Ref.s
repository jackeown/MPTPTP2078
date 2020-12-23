%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gfhfEjmsLs

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 399 expanded)
%              Number of leaves         :   37 ( 131 expanded)
%              Depth                    :   23
%              Number of atoms          : 1361 (5148 expanded)
%              Number of equality atoms :   94 ( 301 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k8_relset_1 @ X35 @ X36 @ X37 @ X36 )
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('2',plain,
    ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A )
    = ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('4',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k8_relset_1 @ X32 @ X33 @ X31 @ X34 )
        = ( k10_relat_1 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k10_relat_1 @ sk_C @ sk_A )
    = ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v5_relat_1 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('9',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('13',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('14',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['11','14'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('16',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X16 ) @ X17 )
      | ( ( k5_relat_1 @ X16 @ ( k6_relat_1 @ X17 ) )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_A ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('19',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_A ) )
    = sk_C ),
    inference(demod,[status(thm)],['17','18'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('20',plain,(
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

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) )
        = ( k10_relat_1 @ X11 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('23',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['19','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('27',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['6','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('31',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k7_relset_1 @ X28 @ X29 @ X27 @ X30 )
        = ( k9_relat_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('38',plain,(
    v4_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12
        = ( k7_relat_1 @ X12 @ X13 ) )
      | ~ ( v4_relat_1 @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('42',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) )
        = ( k9_relat_1 @ X8 @ X9 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('44',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('46',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k2_relat_1 @ sk_C ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['35','46'])).

thf('48',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','47'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['49'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('51',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ( v4_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12
        = ( k7_relat_1 @ X12 @ X13 ) )
      | ~ ( v4_relat_1 @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) )
        = ( k9_relat_1 @ X8 @ X9 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('60',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['33'])).

thf('61',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('65',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('66',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['61','62','63','66'])).

thf('68',plain,
    ( ( ( ( k2_relat_1 @ sk_C )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['58','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('70',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
    = ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['33'])).

thf('73',plain,(
    ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
 != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['71','72'])).

thf('74',plain,(
    ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
 != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['48','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('78',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) )
        = ( k9_relat_1 @ X8 @ X9 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('79',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['49'])).

thf('80',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ( v5_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['77','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['76','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('91',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) )
        = ( k9_relat_1 @ X8 @ X9 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('92',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ( v5_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( v5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ X0 )
      | ( v5_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('96',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('97',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('98',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ X0 )
      | ( v5_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95','96','97','98'])).

thf('100',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( v5_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['89','99'])).

thf('101',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('102',plain,(
    v5_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('104',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('106',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X16 ) @ X17 )
      | ( ( k5_relat_1 @ X16 @ ( k6_relat_1 @ X17 ) )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('108',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('110',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) )
    = sk_C ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['75','110'])).

thf('112',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('113',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    = sk_C ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('115',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('117',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['74','117'])).

thf('119',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['28','118'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gfhfEjmsLs
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:07:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 125 iterations in 0.059s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.51  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.51  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.51  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.51  thf(t39_relset_1, conjecture,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.21/0.51       ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.21/0.51           ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.21/0.51         ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.21/0.51           ( k1_relset_1 @ B @ A @ C ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.51        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.21/0.51          ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.21/0.51              ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.21/0.51            ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.21/0.51              ( k1_relset_1 @ B @ A @ C ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t39_relset_1])).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t38_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.21/0.51         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.21/0.51         (((k8_relset_1 @ X35 @ X36 @ X37 @ X36)
% 0.21/0.51            = (k1_relset_1 @ X35 @ X36 @ X37))
% 0.21/0.51          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.21/0.51      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A)
% 0.21/0.51         = (k1_relset_1 @ sk_B @ sk_A @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(redefinition_k8_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.21/0.51          | ((k8_relset_1 @ X32 @ X33 @ X31 @ X34) = (k10_relat_1 @ X31 @ X34)))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (((k10_relat_1 @ sk_C @ sk_A) = (k1_relset_1 @ sk_B @ sk_A @ sk_C))),
% 0.21/0.51      inference('demod', [status(thm)], ['2', '5'])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(cc2_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.51         ((v5_relat_1 @ X21 @ X23)
% 0.21/0.51          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.51  thf('9', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf(d19_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ B ) =>
% 0.21/0.51       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i]:
% 0.21/0.51         (~ (v5_relat_1 @ X5 @ X6)
% 0.21/0.51          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.21/0.51          | ~ (v1_relat_1 @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(cc1_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( v1_relat_1 @ C ) ))).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.51         ((v1_relat_1 @ X18)
% 0.21/0.51          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.51  thf('14', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('15', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['11', '14'])).
% 0.21/0.51  thf(t79_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ B ) =>
% 0.21/0.51       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.21/0.51         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i]:
% 0.21/0.51         (~ (r1_tarski @ (k2_relat_1 @ X16) @ X17)
% 0.21/0.51          | ((k5_relat_1 @ X16 @ (k6_relat_1 @ X17)) = (X16))
% 0.21/0.51          | ~ (v1_relat_1 @ X16))),
% 0.21/0.51      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.51        | ((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_A)) = (sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.51  thf('18', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('19', plain, (((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_A)) = (sk_C))),
% 0.21/0.51      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.51  thf(t71_relat_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.51       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.51  thf('20', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 0.21/0.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.51  thf(t182_relat_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( v1_relat_1 @ B ) =>
% 0.21/0.51           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.21/0.51             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X10)
% 0.21/0.51          | ((k1_relat_1 @ (k5_relat_1 @ X11 @ X10))
% 0.21/0.51              = (k10_relat_1 @ X11 @ (k1_relat_1 @ X10)))
% 0.21/0.51          | ~ (v1_relat_1 @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.21/0.51            = (k10_relat_1 @ X1 @ X0))
% 0.21/0.51          | ~ (v1_relat_1 @ X1)
% 0.21/0.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['20', '21'])).
% 0.21/0.51  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.21/0.51  thf('23', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.21/0.51            = (k10_relat_1 @ X1 @ X0))
% 0.21/0.51          | ~ (v1_relat_1 @ X1))),
% 0.21/0.51      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      ((((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_A))
% 0.21/0.51        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.51      inference('sup+', [status(thm)], ['19', '24'])).
% 0.21/0.51  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('27', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (((k1_relat_1 @ sk_C) = (k1_relset_1 @ sk_B @ sk_A @ sk_C))),
% 0.21/0.51      inference('demod', [status(thm)], ['6', '27'])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(redefinition_k7_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.21/0.51          | ((k7_relset_1 @ X28 @ X29 @ X27 @ X30) = (k9_relat_1 @ X27 @ X30)))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.51          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.51          != (k2_relset_1 @ sk_B @ sk_A @ sk_C))
% 0.21/0.51        | ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.51            (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.51            != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.51          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.51          != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.21/0.51         <= (~
% 0.21/0.51             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.51                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.51                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.51      inference('split', [status(esa)], ['33'])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ (k9_relat_1 @ sk_C @ sk_B))
% 0.21/0.51          != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.21/0.51         <= (~
% 0.21/0.51             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.51                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.51                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['32', '34'])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.51         ((v4_relat_1 @ X21 @ X22)
% 0.21/0.51          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.51  thf('38', plain, ((v4_relat_1 @ sk_C @ sk_B)),
% 0.21/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.51  thf(t209_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.21/0.51       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i]:
% 0.21/0.51         (((X12) = (k7_relat_1 @ X12 @ X13))
% 0.21/0.51          | ~ (v4_relat_1 @ X12 @ X13)
% 0.21/0.51          | ~ (v1_relat_1 @ X12))),
% 0.21/0.51      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.51  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('42', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.51  thf(t148_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ B ) =>
% 0.21/0.51       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      (![X8 : $i, X9 : $i]:
% 0.21/0.51         (((k2_relat_1 @ (k7_relat_1 @ X8 @ X9)) = (k9_relat_1 @ X8 @ X9))
% 0.21/0.51          | ~ (v1_relat_1 @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))
% 0.21/0.51        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.51      inference('sup+', [status(thm)], ['42', '43'])).
% 0.21/0.51  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('46', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ (k2_relat_1 @ sk_C))
% 0.21/0.51          != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.21/0.51         <= (~
% 0.21/0.51             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.51                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.51                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.51      inference('demod', [status(thm)], ['35', '46'])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      ((((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C))
% 0.21/0.51          != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.21/0.51         <= (~
% 0.21/0.51             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.51                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.51                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['29', '47'])).
% 0.21/0.51  thf(d10_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.51  thf('50', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.51      inference('simplify', [status(thm)], ['49'])).
% 0.21/0.51  thf(d18_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ B ) =>
% 0.21/0.51       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (![X3 : $i, X4 : $i]:
% 0.21/0.51         (~ (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 0.21/0.51          | (v4_relat_1 @ X3 @ X4)
% 0.21/0.51          | ~ (v1_relat_1 @ X3))),
% 0.21/0.51      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.21/0.51  thf('52', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i]:
% 0.21/0.51         (((X12) = (k7_relat_1 @ X12 @ X13))
% 0.21/0.51          | ~ (v4_relat_1 @ X12 @ X13)
% 0.21/0.51          | ~ (v1_relat_1 @ X12))),
% 0.21/0.51      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | ((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.51  thf('55', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))) | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['54'])).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      (![X8 : $i, X9 : $i]:
% 0.21/0.51         (((k2_relat_1 @ (k7_relat_1 @ X8 @ X9)) = (k9_relat_1 @ X8 @ X9))
% 0.21/0.51          | ~ (v1_relat_1 @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.51  thf('57', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['55', '56'])).
% 0.21/0.51  thf('58', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X0)
% 0.21/0.51          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['57'])).
% 0.21/0.51  thf('59', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.51  thf('60', plain,
% 0.21/0.51      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.51          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.51          != (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.21/0.51         <= (~
% 0.21/0.51             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.51                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.51                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.51      inference('split', [status(esa)], ['33'])).
% 0.21/0.51  thf('61', plain,
% 0.21/0.51      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ (k10_relat_1 @ sk_C @ sk_A))
% 0.21/0.51          != (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.21/0.51         <= (~
% 0.21/0.51             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.51                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.51                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.51  thf('62', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.51  thf('63', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.51  thf('64', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.51  thf('65', plain,
% 0.21/0.51      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.51         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 0.21/0.51          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.51  thf('66', plain,
% 0.21/0.51      (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.51  thf('67', plain,
% 0.21/0.51      ((((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.21/0.51         <= (~
% 0.21/0.51             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.51                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.51                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.51      inference('demod', [status(thm)], ['61', '62', '63', '66'])).
% 0.21/0.51  thf('68', plain,
% 0.21/0.51      (((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)) | ~ (v1_relat_1 @ sk_C)))
% 0.21/0.51         <= (~
% 0.21/0.51             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.51                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.51                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['58', '67'])).
% 0.21/0.51  thf('69', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('70', plain,
% 0.21/0.51      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.21/0.51         <= (~
% 0.21/0.51             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.51                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.51                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.51      inference('demod', [status(thm)], ['68', '69'])).
% 0.21/0.51  thf('71', plain,
% 0.21/0.51      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.51          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.51          = (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['70'])).
% 0.21/0.51  thf('72', plain,
% 0.21/0.51      (~
% 0.21/0.51       (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.51          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.51          = (k1_relset_1 @ sk_B @ sk_A @ sk_C))) | 
% 0.21/0.51       ~
% 0.21/0.51       (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.51          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.51          = (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.21/0.51      inference('split', [status(esa)], ['33'])).
% 0.21/0.51  thf('73', plain,
% 0.21/0.51      (~
% 0.21/0.51       (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.51          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.51          = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['71', '72'])).
% 0.21/0.51  thf('74', plain,
% 0.21/0.51      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C))
% 0.21/0.51         != (k1_relset_1 @ sk_B @ sk_A @ sk_C))),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['48', '73'])).
% 0.21/0.51  thf('75', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X0)
% 0.21/0.51          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['57'])).
% 0.21/0.51  thf('76', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))) | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['54'])).
% 0.21/0.51  thf('77', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))) | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['54'])).
% 0.21/0.51  thf('78', plain,
% 0.21/0.51      (![X8 : $i, X9 : $i]:
% 0.21/0.51         (((k2_relat_1 @ (k7_relat_1 @ X8 @ X9)) = (k9_relat_1 @ X8 @ X9))
% 0.21/0.51          | ~ (v1_relat_1 @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.51  thf('79', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.51      inference('simplify', [status(thm)], ['49'])).
% 0.21/0.51  thf('80', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i]:
% 0.21/0.51         (~ (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.21/0.51          | (v5_relat_1 @ X5 @ X6)
% 0.21/0.51          | ~ (v1_relat_1 @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.51  thf('81', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['79', '80'])).
% 0.21/0.51  thf('82', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.21/0.51          | ~ (v1_relat_1 @ X1)
% 0.21/0.51          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['78', '81'])).
% 0.21/0.51  thf('83', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | (v5_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ 
% 0.21/0.51             (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['77', '82'])).
% 0.21/0.51  thf('84', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v5_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ 
% 0.21/0.51           (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.21/0.51          | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['83'])).
% 0.21/0.51  thf('85', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v5_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['76', '84'])).
% 0.21/0.51  thf('86', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X0)
% 0.21/0.51          | (v5_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['85'])).
% 0.21/0.51  thf('87', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i]:
% 0.21/0.51         (~ (v5_relat_1 @ X5 @ X6)
% 0.21/0.51          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.21/0.51          | ~ (v1_relat_1 @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.51  thf('88', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | (r1_tarski @ (k2_relat_1 @ X0) @ 
% 0.21/0.51             (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['86', '87'])).
% 0.21/0.51  thf('89', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r1_tarski @ (k2_relat_1 @ X0) @ 
% 0.21/0.51           (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.21/0.51          | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['88'])).
% 0.21/0.51  thf('90', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.51  thf('91', plain,
% 0.21/0.51      (![X8 : $i, X9 : $i]:
% 0.21/0.51         (((k2_relat_1 @ (k7_relat_1 @ X8 @ X9)) = (k9_relat_1 @ X8 @ X9))
% 0.21/0.51          | ~ (v1_relat_1 @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.51  thf('92', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i]:
% 0.21/0.51         (~ (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.21/0.51          | (v5_relat_1 @ X5 @ X6)
% 0.21/0.51          | ~ (v1_relat_1 @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.51  thf('93', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 0.21/0.51          | ~ (v1_relat_1 @ X1)
% 0.21/0.51          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.21/0.51          | (v5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2))),
% 0.21/0.51      inference('sup-', [status(thm)], ['91', '92'])).
% 0.21/0.51  thf('94', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (r1_tarski @ (k2_relat_1 @ sk_C) @ X0)
% 0.21/0.51          | (v5_relat_1 @ (k7_relat_1 @ sk_C @ sk_B) @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_B))
% 0.21/0.51          | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['90', '93'])).
% 0.21/0.51  thf('95', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.51  thf('96', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.51  thf('97', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('98', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('99', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (r1_tarski @ (k2_relat_1 @ sk_C) @ X0) | (v5_relat_1 @ sk_C @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['94', '95', '96', '97', '98'])).
% 0.21/0.51  thf('100', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.51        | (v5_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['89', '99'])).
% 0.21/0.51  thf('101', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('102', plain,
% 0.21/0.51      ((v5_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.21/0.51      inference('demod', [status(thm)], ['100', '101'])).
% 0.21/0.51  thf('103', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i]:
% 0.21/0.51         (~ (v5_relat_1 @ X5 @ X6)
% 0.21/0.51          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.21/0.51          | ~ (v1_relat_1 @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.51  thf('104', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.51        | (r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.21/0.51           (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['102', '103'])).
% 0.21/0.51  thf('105', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('106', plain,
% 0.21/0.51      ((r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.21/0.51        (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.21/0.51      inference('demod', [status(thm)], ['104', '105'])).
% 0.21/0.51  thf('107', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i]:
% 0.21/0.51         (~ (r1_tarski @ (k2_relat_1 @ X16) @ X17)
% 0.21/0.51          | ((k5_relat_1 @ X16 @ (k6_relat_1 @ X17)) = (X16))
% 0.21/0.51          | ~ (v1_relat_1 @ X16))),
% 0.21/0.51      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.21/0.51  thf('108', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.51        | ((k5_relat_1 @ sk_C @ 
% 0.21/0.51            (k6_relat_1 @ (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))) = (
% 0.21/0.51            sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['106', '107'])).
% 0.21/0.51  thf('109', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('110', plain,
% 0.21/0.51      (((k5_relat_1 @ sk_C @ 
% 0.21/0.51         (k6_relat_1 @ (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))) = (sk_C))),
% 0.21/0.51      inference('demod', [status(thm)], ['108', '109'])).
% 0.21/0.51  thf('111', plain,
% 0.21/0.51      ((((k5_relat_1 @ sk_C @ (k6_relat_1 @ (k2_relat_1 @ sk_C))) = (sk_C))
% 0.21/0.51        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.51      inference('sup+', [status(thm)], ['75', '110'])).
% 0.21/0.51  thf('112', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('113', plain,
% 0.21/0.51      (((k5_relat_1 @ sk_C @ (k6_relat_1 @ (k2_relat_1 @ sk_C))) = (sk_C))),
% 0.21/0.51      inference('demod', [status(thm)], ['111', '112'])).
% 0.21/0.51  thf('114', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.21/0.51            = (k10_relat_1 @ X1 @ X0))
% 0.21/0.51          | ~ (v1_relat_1 @ X1))),
% 0.21/0.51      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.51  thf('115', plain,
% 0.21/0.51      ((((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.21/0.51        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.51      inference('sup+', [status(thm)], ['113', '114'])).
% 0.21/0.51  thf('116', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('117', plain,
% 0.21/0.51      (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 0.21/0.51      inference('demod', [status(thm)], ['115', '116'])).
% 0.21/0.51  thf('118', plain,
% 0.21/0.51      (((k1_relat_1 @ sk_C) != (k1_relset_1 @ sk_B @ sk_A @ sk_C))),
% 0.21/0.51      inference('demod', [status(thm)], ['74', '117'])).
% 0.21/0.51  thf('119', plain, ($false),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['28', '118'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.35/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
