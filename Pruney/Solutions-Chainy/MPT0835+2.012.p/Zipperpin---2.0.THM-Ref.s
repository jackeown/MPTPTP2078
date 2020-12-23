%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EAbjloD5dY

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 339 expanded)
%              Number of leaves         :   35 ( 118 expanded)
%              Depth                    :   11
%              Number of atoms          :  820 (4527 expanded)
%              Number of equality atoms :   61 ( 259 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

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

thf('0',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('6',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','3','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('9',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k7_relset_1 @ X27 @ X28 @ X26 @ X29 )
        = ( k9_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('14',plain,(
    v4_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12
        = ( k7_relat_1 @ X12 @ X13 ) )
      | ~ ( v4_relat_1 @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('18',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('19',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['16','19'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('22',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('24',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k2_relat_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['7','10','11','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('27',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k8_relset_1 @ X31 @ X32 @ X30 @ X33 )
        = ( k10_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('31',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['29','30'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('32',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('35',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['33','34'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('36',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('37',plain,
    ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_A )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('38',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k10_relat_1 @ X9 @ X10 )
        = ( k10_relat_1 @ X9 @ ( k3_xboole_0 @ ( k2_relat_1 @ X9 ) @ X10 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('39',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_A )
      = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('41',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('42',plain,(
    ! [X11: $i] :
      ( ( ( k10_relat_1 @ X11 @ ( k2_relat_1 @ X11 ) )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ ( k9_relat_1 @ sk_C @ sk_B ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('47',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('48',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('49',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['44','45','46','47','48'])).

thf('50',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('51',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('53',plain,
    ( ( k10_relat_1 @ sk_C @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['39','51','52'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('55',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('57',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X34 ) @ X35 )
      | ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('61',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12
        = ( k7_relat_1 @ X12 @ X13 ) )
      | ~ ( v4_relat_1 @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('63',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('65',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('67',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('69',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('71',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('72',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['25','28','53','69','70','71'])).

thf('73',plain,(
    $false ),
    inference(simplify,[status(thm)],['72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EAbjloD5dY
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:24:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 66 iterations in 0.028s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.48  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.48  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.48  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.48  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.48  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.48  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.48  thf(t39_relset_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.21/0.48       ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.21/0.48           ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.21/0.48         ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.21/0.48           ( k1_relset_1 @ B @ A @ C ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.48        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.21/0.48          ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.21/0.48              ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.21/0.48            ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.21/0.48              ( k1_relset_1 @ B @ A @ C ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t39_relset_1])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.48          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.48          != (k2_relset_1 @ sk_B @ sk_A @ sk_C))
% 0.21/0.48        | ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.48            (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.48            != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.48       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.48         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 0.21/0.48          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.48  thf('3', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.48       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.48         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 0.21/0.48          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.48  thf('6', plain, (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.21/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.48          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A)) != (k2_relat_1 @ sk_C))
% 0.21/0.48        | ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.48            (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B)) != (k1_relat_1 @ sk_C)))),
% 0.21/0.48      inference('demod', [status(thm)], ['0', '3', '6'])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(redefinition_k7_relset_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.48       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.21/0.48          | ((k7_relset_1 @ X27 @ X28 @ X26 @ X29) = (k9_relat_1 @ X26 @ X29)))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(cc2_relset_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.48       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.48         ((v4_relat_1 @ X17 @ X18)
% 0.21/0.48          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.21/0.48      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.48  thf('14', plain, ((v4_relat_1 @ sk_C @ sk_B)),
% 0.21/0.48      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf(t209_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.21/0.48       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X12 : $i, X13 : $i]:
% 0.21/0.48         (((X12) = (k7_relat_1 @ X12 @ X13))
% 0.21/0.48          | ~ (v4_relat_1 @ X12 @ X13)
% 0.21/0.48          | ~ (v1_relat_1 @ X12))),
% 0.21/0.48      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(cc1_relset_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.48       ( v1_relat_1 @ C ) ))).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.48         ((v1_relat_1 @ X14)
% 0.21/0.48          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.21/0.48      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.48  thf('19', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('20', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['16', '19'])).
% 0.21/0.48  thf(t148_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ B ) =>
% 0.21/0.48       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i]:
% 0.21/0.48         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 0.21/0.48          | ~ (v1_relat_1 @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))
% 0.21/0.48        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.48      inference('sup+', [status(thm)], ['20', '21'])).
% 0.21/0.48  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('24', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      ((((k9_relat_1 @ sk_C @ (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.48          != (k2_relat_1 @ sk_C))
% 0.21/0.48        | ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ (k2_relat_1 @ sk_C))
% 0.21/0.48            != (k1_relat_1 @ sk_C)))),
% 0.21/0.48      inference('demod', [status(thm)], ['7', '10', '11', '24'])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(redefinition_k8_relset_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.48       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.21/0.48          | ((k8_relset_1 @ X31 @ X32 @ X30 @ X33) = (k10_relat_1 @ X30 @ X33)))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.48         ((v5_relat_1 @ X17 @ X19)
% 0.21/0.48          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.21/0.48      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.48  thf('31', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.21/0.48      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.48  thf(d19_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ B ) =>
% 0.21/0.48       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      (![X5 : $i, X6 : $i]:
% 0.21/0.48         (~ (v5_relat_1 @ X5 @ X6)
% 0.21/0.48          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.21/0.48          | ~ (v1_relat_1 @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.48  thf('33', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.48  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('35', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)),
% 0.21/0.48      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.48  thf(t28_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      (![X3 : $i, X4 : $i]:
% 0.21/0.48         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.21/0.48      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      (((k3_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_A) = (k2_relat_1 @ sk_C))),
% 0.21/0.48      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.48  thf(t168_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ B ) =>
% 0.21/0.48       ( ( k10_relat_1 @ B @ A ) =
% 0.21/0.48         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 0.21/0.48  thf('38', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i]:
% 0.21/0.48         (((k10_relat_1 @ X9 @ X10)
% 0.21/0.48            = (k10_relat_1 @ X9 @ (k3_xboole_0 @ (k2_relat_1 @ X9) @ X10)))
% 0.21/0.48          | ~ (v1_relat_1 @ X9))),
% 0.21/0.48      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.21/0.48  thf('39', plain,
% 0.21/0.48      ((((k10_relat_1 @ sk_C @ sk_A)
% 0.21/0.48          = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.21/0.48        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.48      inference('sup+', [status(thm)], ['37', '38'])).
% 0.21/0.48  thf('40', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['16', '19'])).
% 0.21/0.48  thf('41', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i]:
% 0.21/0.48         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 0.21/0.48          | ~ (v1_relat_1 @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.48  thf(t169_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.21/0.48  thf('42', plain,
% 0.21/0.48      (![X11 : $i]:
% 0.21/0.48         (((k10_relat_1 @ X11 @ (k2_relat_1 @ X11)) = (k1_relat_1 @ X11))
% 0.21/0.48          | ~ (v1_relat_1 @ X11))),
% 0.21/0.48      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.21/0.48  thf('43', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.21/0.48            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.21/0.48          | ~ (v1_relat_1 @ X1)
% 0.21/0.48          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.21/0.48      inference('sup+', [status(thm)], ['41', '42'])).
% 0.21/0.48  thf('44', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.48        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.48        | ((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_B) @ 
% 0.21/0.48            (k9_relat_1 @ sk_C @ sk_B))
% 0.21/0.48            = (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_B))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['40', '43'])).
% 0.21/0.48  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('47', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['16', '19'])).
% 0.21/0.48  thf('48', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['16', '19'])).
% 0.21/0.48  thf('49', plain,
% 0.21/0.48      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) = (k1_relat_1 @ sk_C))),
% 0.21/0.48      inference('demod', [status(thm)], ['44', '45', '46', '47', '48'])).
% 0.21/0.48  thf('50', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf('51', plain,
% 0.21/0.48      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.21/0.48      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.48  thf('52', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('53', plain, (((k10_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.21/0.48      inference('demod', [status(thm)], ['39', '51', '52'])).
% 0.21/0.48  thf(d10_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.48  thf('54', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.48  thf('55', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.48      inference('simplify', [status(thm)], ['54'])).
% 0.21/0.48  thf('56', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t13_relset_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.21/0.48       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 0.21/0.48         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.21/0.48  thf('57', plain,
% 0.21/0.48      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.21/0.48         (~ (r1_tarski @ (k1_relat_1 @ X34) @ X35)
% 0.21/0.48          | (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.21/0.48          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 0.21/0.48      inference('cnf', [status(esa)], [t13_relset_1])).
% 0.21/0.48  thf('58', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A)))
% 0.21/0.48          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.48  thf('59', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_C @ 
% 0.21/0.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['55', '58'])).
% 0.21/0.48  thf('60', plain,
% 0.21/0.48      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.48         ((v4_relat_1 @ X17 @ X18)
% 0.21/0.48          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.21/0.48      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.48  thf('61', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.21/0.48      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.48  thf('62', plain,
% 0.21/0.48      (![X12 : $i, X13 : $i]:
% 0.21/0.48         (((X12) = (k7_relat_1 @ X12 @ X13))
% 0.21/0.48          | ~ (v4_relat_1 @ X12 @ X13)
% 0.21/0.48          | ~ (v1_relat_1 @ X12))),
% 0.21/0.48      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.21/0.48  thf('63', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.48        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.48  thf('64', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('65', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.21/0.48      inference('demod', [status(thm)], ['63', '64'])).
% 0.21/0.48  thf('66', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i]:
% 0.21/0.48         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 0.21/0.48          | ~ (v1_relat_1 @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.48  thf('67', plain,
% 0.21/0.48      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 0.21/0.48        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.48      inference('sup+', [status(thm)], ['65', '66'])).
% 0.21/0.48  thf('68', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('69', plain,
% 0.21/0.48      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.21/0.48      inference('demod', [status(thm)], ['67', '68'])).
% 0.21/0.48  thf('70', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.48  thf('71', plain,
% 0.21/0.48      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.21/0.48      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.48  thf('72', plain,
% 0.21/0.48      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.21/0.48        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))),
% 0.21/0.48      inference('demod', [status(thm)], ['25', '28', '53', '69', '70', '71'])).
% 0.21/0.48  thf('73', plain, ($false), inference('simplify', [status(thm)], ['72'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
