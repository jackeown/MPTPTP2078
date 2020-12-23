%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4nEHDaPsIi

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 414 expanded)
%              Number of leaves         :   36 ( 140 expanded)
%              Depth                    :   14
%              Number of atoms          : 1036 (5201 expanded)
%              Number of equality atoms :   76 ( 286 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

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
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X35 ) @ X36 )
      | ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ( X16
        = ( k7_relat_1 @ X16 @ X17 ) )
      | ~ ( v4_relat_1 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k8_relset_1 @ X32 @ X33 @ X31 @ X34 )
        = ( k10_relat_1 @ X31 @ X34 ) ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v5_relat_1 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ~ ( v5_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
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

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('33',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('34',plain,
    ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_A )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('35',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k10_relat_1 @ X13 @ X14 )
        = ( k10_relat_1 @ X13 @ ( k3_xboole_0 @ ( k2_relat_1 @ X13 ) @ X14 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('36',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_A )
      = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('39',plain,(
    v4_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X16
        = ( k7_relat_1 @ X16 @ X17 ) )
      | ~ ( v4_relat_1 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['12','13'])).

thf('43',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('45',plain,(
    ! [X15: $i] :
      ( ( ( k10_relat_1 @ X15 @ ( k2_relat_1 @ X15 ) )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ ( k9_relat_1 @ sk_C @ sk_B ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['12','13'])).

thf('49',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['12','13'])).

thf('50',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('51',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('52',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['47','48','49','50','51'])).

thf('53',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('54',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('55',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['12','13'])).

thf('57',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['52','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['12','13'])).

thf('60',plain,
    ( ( k10_relat_1 @ sk_C @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['36','58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('62',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k7_relset_1 @ X28 @ X29 @ X27 @ X30 )
        = ( k9_relat_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

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
    inference(demod,[status(thm)],['25','60','63','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('70',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['23'])).

thf('71',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('74',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('75',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k2_relat_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['71','72','75'])).

thf('77',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['68','76'])).

thf('78',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['52','57'])).

thf('79',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    = ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['23'])).

thf('82',plain,(
    ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
 != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['80','81'])).

thf('83',plain,(
    ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['67','82'])).

thf('84',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['19','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4nEHDaPsIi
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:02:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 63 iterations in 0.030s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.49  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.49  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.49  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.49  thf(d10_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.49  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.49      inference('simplify', [status(thm)], ['0'])).
% 0.21/0.49  thf(t39_relset_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.21/0.49       ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.21/0.49           ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.21/0.49         ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.21/0.49           ( k1_relset_1 @ B @ A @ C ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.49        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.21/0.49          ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.21/0.49              ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.21/0.49            ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.21/0.49              ( k1_relset_1 @ B @ A @ C ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t39_relset_1])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t13_relset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.21/0.49       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 0.21/0.49         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.21/0.49         (~ (r1_tarski @ (k1_relat_1 @ X35) @ X36)
% 0.21/0.49          | (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.21/0.49          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 0.21/0.49      inference('cnf', [status(esa)], [t13_relset_1])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A)))
% 0.21/0.49          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C @ 
% 0.21/0.49        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.49  thf(cc2_relset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.49       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.49         ((v4_relat_1 @ X18 @ X19)
% 0.21/0.49          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.21/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.49  thf('7', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf(t209_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.21/0.49       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X16 : $i, X17 : $i]:
% 0.21/0.49         (((X16) = (k7_relat_1 @ X16 @ X17))
% 0.21/0.49          | ~ (v4_relat_1 @ X16 @ X17)
% 0.21/0.49          | ~ (v1_relat_1 @ X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.49        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(cc2_relat_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.21/0.49          | (v1_relat_1 @ X5)
% 0.21/0.49          | ~ (v1_relat_1 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf(fc6_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.49  thf('14', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('15', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.21/0.49      inference('demod', [status(thm)], ['9', '14'])).
% 0.21/0.49  thf(t148_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ B ) =>
% 0.21/0.49       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X11 : $i, X12 : $i]:
% 0.21/0.49         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.21/0.49          | ~ (v1_relat_1 @ X11))),
% 0.21/0.49      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 0.21/0.49        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.49      inference('sup+', [status(thm)], ['15', '16'])).
% 0.21/0.49  thf('18', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.21/0.49      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(redefinition_k8_relset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.49       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.21/0.49          | ((k8_relset_1 @ X32 @ X33 @ X31 @ X34) = (k10_relat_1 @ X31 @ X34)))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.49          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.49          != (k2_relset_1 @ sk_B @ sk_A @ sk_C))
% 0.21/0.49        | ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.49            (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.49            != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.49          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.49          != (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.21/0.49         <= (~
% 0.21/0.49             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.49                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.49                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.49      inference('split', [status(esa)], ['23'])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ (k10_relat_1 @ sk_C @ sk_A))
% 0.21/0.49          != (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.21/0.49         <= (~
% 0.21/0.49             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.49                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.49                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['22', '24'])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.49         ((v5_relat_1 @ X18 @ X20)
% 0.21/0.49          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.21/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.49  thf('28', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.21/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.49  thf(d19_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ B ) =>
% 0.21/0.49       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i]:
% 0.21/0.49         (~ (v5_relat_1 @ X7 @ X8)
% 0.21/0.49          | (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 0.21/0.49          | ~ (v1_relat_1 @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.49  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('32', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.49  thf(t28_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i]:
% 0.21/0.49         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (((k3_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_A) = (k2_relat_1 @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.49  thf(t168_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ B ) =>
% 0.21/0.49       ( ( k10_relat_1 @ B @ A ) =
% 0.21/0.49         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i]:
% 0.21/0.49         (((k10_relat_1 @ X13 @ X14)
% 0.21/0.49            = (k10_relat_1 @ X13 @ (k3_xboole_0 @ (k2_relat_1 @ X13) @ X14)))
% 0.21/0.49          | ~ (v1_relat_1 @ X13))),
% 0.21/0.49      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      ((((k10_relat_1 @ sk_C @ sk_A)
% 0.21/0.49          = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.21/0.49        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.49      inference('sup+', [status(thm)], ['34', '35'])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.49         ((v4_relat_1 @ X18 @ X19)
% 0.21/0.49          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.21/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.49  thf('39', plain, ((v4_relat_1 @ sk_C @ sk_B)),
% 0.21/0.49      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      (![X16 : $i, X17 : $i]:
% 0.21/0.49         (((X16) = (k7_relat_1 @ X16 @ X17))
% 0.21/0.49          | ~ (v4_relat_1 @ X16 @ X17)
% 0.21/0.49          | ~ (v1_relat_1 @ X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.49  thf('42', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('43', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      (![X11 : $i, X12 : $i]:
% 0.21/0.49         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.21/0.49          | ~ (v1_relat_1 @ X11))),
% 0.21/0.49      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.49  thf(t169_relat_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      (![X15 : $i]:
% 0.21/0.49         (((k10_relat_1 @ X15 @ (k2_relat_1 @ X15)) = (k1_relat_1 @ X15))
% 0.21/0.49          | ~ (v1_relat_1 @ X15))),
% 0.21/0.49      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.21/0.49  thf('46', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.21/0.49            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.21/0.49          | ~ (v1_relat_1 @ X1)
% 0.21/0.49          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['44', '45'])).
% 0.21/0.49  thf('47', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.49        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.49        | ((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_B) @ 
% 0.21/0.49            (k9_relat_1 @ sk_C @ sk_B))
% 0.21/0.49            = (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_B))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['43', '46'])).
% 0.21/0.49  thf('48', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('49', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('50', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.49  thf('51', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.49  thf('52', plain,
% 0.21/0.49      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) = (k1_relat_1 @ sk_C))),
% 0.21/0.49      inference('demod', [status(thm)], ['47', '48', '49', '50', '51'])).
% 0.21/0.49  thf('53', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.49  thf('54', plain,
% 0.21/0.49      (![X11 : $i, X12 : $i]:
% 0.21/0.49         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.21/0.49          | ~ (v1_relat_1 @ X11))),
% 0.21/0.49      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.49  thf('55', plain,
% 0.21/0.49      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))
% 0.21/0.49        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.49      inference('sup+', [status(thm)], ['53', '54'])).
% 0.21/0.49  thf('56', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('57', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['55', '56'])).
% 0.21/0.49  thf('58', plain,
% 0.21/0.49      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.21/0.49      inference('demod', [status(thm)], ['52', '57'])).
% 0.21/0.49  thf('59', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('60', plain, (((k10_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.21/0.49      inference('demod', [status(thm)], ['36', '58', '59'])).
% 0.21/0.49  thf('61', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(redefinition_k7_relset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.49       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.21/0.49  thf('62', plain,
% 0.21/0.49      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.21/0.49          | ((k7_relset_1 @ X28 @ X29 @ X27 @ X30) = (k9_relat_1 @ X27 @ X30)))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.21/0.49  thf('63', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.49  thf('64', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.49       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.49  thf('65', plain,
% 0.21/0.49      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.49         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 0.21/0.49          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.49  thf('66', plain,
% 0.21/0.49      (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.49  thf('67', plain,
% 0.21/0.49      ((((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.21/0.49         <= (~
% 0.21/0.49             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.49                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.49                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.49      inference('demod', [status(thm)], ['25', '60', '63', '66'])).
% 0.21/0.49  thf('68', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.49  thf('69', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.49  thf('70', plain,
% 0.21/0.49      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.49          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.49          != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.21/0.49         <= (~
% 0.21/0.49             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.49                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.49                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.49      inference('split', [status(esa)], ['23'])).
% 0.21/0.49  thf('71', plain,
% 0.21/0.49      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ (k9_relat_1 @ sk_C @ sk_B))
% 0.21/0.49          != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.21/0.49         <= (~
% 0.21/0.49             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.49                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.49                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['69', '70'])).
% 0.21/0.49  thf('72', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['55', '56'])).
% 0.21/0.49  thf('73', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.49       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.49  thf('74', plain,
% 0.21/0.49      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.49         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 0.21/0.49          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.49  thf('75', plain,
% 0.21/0.49      (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['73', '74'])).
% 0.21/0.49  thf('76', plain,
% 0.21/0.49      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ (k2_relat_1 @ sk_C))
% 0.21/0.49          != (k1_relat_1 @ sk_C)))
% 0.21/0.49         <= (~
% 0.21/0.49             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.49                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.49                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.49      inference('demod', [status(thm)], ['71', '72', '75'])).
% 0.21/0.49  thf('77', plain,
% 0.21/0.49      ((((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 0.21/0.49         <= (~
% 0.21/0.49             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.49                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.49                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['68', '76'])).
% 0.21/0.49  thf('78', plain,
% 0.21/0.49      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.21/0.49      inference('demod', [status(thm)], ['52', '57'])).
% 0.21/0.49  thf('79', plain,
% 0.21/0.49      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 0.21/0.49         <= (~
% 0.21/0.49             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.49                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.49                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.49      inference('demod', [status(thm)], ['77', '78'])).
% 0.21/0.49  thf('80', plain,
% 0.21/0.49      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.49          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.49          = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['79'])).
% 0.21/0.49  thf('81', plain,
% 0.21/0.49      (~
% 0.21/0.49       (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.49          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.49          = (k2_relset_1 @ sk_B @ sk_A @ sk_C))) | 
% 0.21/0.49       ~
% 0.21/0.49       (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.49          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.49          = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.21/0.49      inference('split', [status(esa)], ['23'])).
% 0.21/0.49  thf('82', plain,
% 0.21/0.49      (~
% 0.21/0.49       (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.49          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.49          = (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['80', '81'])).
% 0.21/0.49  thf('83', plain,
% 0.21/0.49      (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['67', '82'])).
% 0.21/0.49  thf('84', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['19', '83'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
