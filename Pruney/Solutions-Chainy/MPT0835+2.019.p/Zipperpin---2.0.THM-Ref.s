%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BJ94oQ8Scn

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 263 expanded)
%              Number of leaves         :   31 (  90 expanded)
%              Depth                    :   15
%              Number of atoms          : 1001 (3829 expanded)
%              Number of equality atoms :   78 ( 229 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

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

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k8_relset_1 @ X26 @ X27 @ X25 @ X28 )
        = ( k10_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('4',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( ( k7_relset_1 @ X22 @ X23 @ X21 @ X24 )
        = ( k9_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('11',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('16',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['6'])).

thf('17',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('20',plain,(
    v4_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X6
        = ( k7_relat_1 @ X6 @ X7 ) )
      | ~ ( v4_relat_1 @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('24',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('25',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['22','25'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) )
        = ( k9_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('28',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['23','24'])).

thf('30',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('32',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('33',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k2_relat_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['17','30','33'])).

thf('35',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','34'])).

thf('36',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('37',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) )
        = ( k9_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('38',plain,(
    ! [X5: $i] :
      ( ( ( k10_relat_1 @ X5 @ ( k2_relat_1 @ X5 ) )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ ( k9_relat_1 @ sk_C @ sk_B ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['23','24'])).

thf('42',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['23','24'])).

thf('43',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('44',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('45',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['40','41','42','43','44'])).

thf('46',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('47',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['35','47'])).

thf('49',plain,
    ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    = ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['6'])).

thf('51',plain,(
    ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
 != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['49','50'])).

thf('52',plain,(
    ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['13','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('54',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k8_relset_1 @ X29 @ X30 @ X31 @ X30 )
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('55',plain,
    ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A )
    = ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('57',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('58',plain,
    ( ( k10_relat_1 @ sk_C @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('59',plain,(
    ! [X8: $i] :
      ( ( ( k7_relat_1 @ X8 @ ( k1_relat_1 @ X8 ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('60',plain,(
    v4_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc23_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v4_relat_1 @ C @ B ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) )
        & ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ A )
        & ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ) )).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v4_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X1 )
      | ~ ( v4_relat_1 @ X0 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc23_relat_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( v4_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['23','24'])).

thf('64',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['59','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['23','24'])).

thf('67',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X6
        = ( k7_relat_1 @ X6 @ X7 ) )
      | ~ ( v4_relat_1 @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('69',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['23','24'])).

thf('71',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) )
        = ( k9_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('73',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['23','24'])).

thf('75',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['52','58','75'])).

thf('77',plain,(
    $false ),
    inference(simplify,[status(thm)],['76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BJ94oQ8Scn
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:30:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 171 iterations in 0.096s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.56  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.56  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.56  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.56  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.56  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.56  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.56  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.56  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.56  thf(t39_relset_1, conjecture,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.56       ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.20/0.56           ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.20/0.56         ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.20/0.56           ( k1_relset_1 @ B @ A @ C ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.56        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.56          ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.20/0.56              ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.20/0.56            ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.20/0.56              ( k1_relset_1 @ B @ A @ C ) ) ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t39_relset_1])).
% 0.20/0.56  thf('0', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(redefinition_k8_relset_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.56       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.37/0.56  thf('1', plain,
% 0.37/0.56      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.37/0.56          | ((k8_relset_1 @ X26 @ X27 @ X25 @ X28) = (k10_relat_1 @ X25 @ X28)))),
% 0.37/0.56      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.37/0.56  thf('2', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.56  thf('3', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(redefinition_k7_relset_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.56       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.37/0.56  thf('4', plain,
% 0.37/0.56      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.37/0.56          | ((k7_relset_1 @ X22 @ X23 @ X21 @ X24) = (k9_relat_1 @ X21 @ X24)))),
% 0.37/0.56      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.37/0.56  thf('5', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.56  thf('6', plain,
% 0.37/0.56      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.37/0.56          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.37/0.56          != (k2_relset_1 @ sk_B @ sk_A @ sk_C))
% 0.37/0.56        | ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.37/0.56            (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.37/0.56            != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('7', plain,
% 0.37/0.56      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.37/0.56          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.37/0.56          != (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.37/0.56         <= (~
% 0.37/0.56             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.37/0.56                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.37/0.56                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.37/0.56      inference('split', [status(esa)], ['6'])).
% 0.37/0.56  thf('8', plain,
% 0.37/0.56      ((((k9_relat_1 @ sk_C @ (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.37/0.56          != (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.37/0.56         <= (~
% 0.37/0.56             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.37/0.56                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.37/0.56                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['5', '7'])).
% 0.37/0.56  thf('9', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(redefinition_k2_relset_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.56       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.37/0.56  thf('10', plain,
% 0.37/0.56      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.37/0.56         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 0.37/0.56          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.37/0.56      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.37/0.56  thf('11', plain,
% 0.37/0.56      (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.37/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.56  thf('12', plain,
% 0.37/0.56      ((((k9_relat_1 @ sk_C @ (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.37/0.56          != (k2_relat_1 @ sk_C)))
% 0.37/0.56         <= (~
% 0.37/0.56             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.37/0.56                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.37/0.56                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.37/0.56      inference('demod', [status(thm)], ['8', '11'])).
% 0.37/0.56  thf('13', plain,
% 0.37/0.56      ((((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A))
% 0.37/0.56          != (k2_relat_1 @ sk_C)))
% 0.37/0.56         <= (~
% 0.37/0.56             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.37/0.56                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.37/0.56                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['2', '12'])).
% 0.37/0.56  thf('14', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.56  thf('15', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.56  thf('16', plain,
% 0.37/0.56      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.37/0.56          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.37/0.56          != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.37/0.56         <= (~
% 0.37/0.56             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.37/0.56                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.37/0.56                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.37/0.56      inference('split', [status(esa)], ['6'])).
% 0.37/0.56  thf('17', plain,
% 0.37/0.56      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ (k9_relat_1 @ sk_C @ sk_B))
% 0.37/0.56          != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.37/0.56         <= (~
% 0.37/0.56             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.37/0.56                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.37/0.56                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['15', '16'])).
% 0.37/0.56  thf('18', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(cc2_relset_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.56       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.37/0.56  thf('19', plain,
% 0.37/0.56      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.56         ((v4_relat_1 @ X12 @ X13)
% 0.37/0.56          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.37/0.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.37/0.56  thf('20', plain, ((v4_relat_1 @ sk_C @ sk_B)),
% 0.37/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.56  thf(t209_relat_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.37/0.56       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.37/0.56  thf('21', plain,
% 0.37/0.56      (![X6 : $i, X7 : $i]:
% 0.37/0.56         (((X6) = (k7_relat_1 @ X6 @ X7))
% 0.37/0.56          | ~ (v4_relat_1 @ X6 @ X7)
% 0.37/0.56          | ~ (v1_relat_1 @ X6))),
% 0.37/0.56      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.37/0.56  thf('22', plain,
% 0.37/0.56      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_B)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.37/0.56  thf('23', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(cc1_relset_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.56       ( v1_relat_1 @ C ) ))).
% 0.37/0.56  thf('24', plain,
% 0.37/0.56      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.37/0.56         ((v1_relat_1 @ X9)
% 0.37/0.56          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.37/0.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.37/0.56  thf('25', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.56      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.56  thf('26', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.37/0.56      inference('demod', [status(thm)], ['22', '25'])).
% 0.37/0.56  thf(t148_relat_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( v1_relat_1 @ B ) =>
% 0.37/0.56       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.37/0.56  thf('27', plain,
% 0.37/0.56      (![X3 : $i, X4 : $i]:
% 0.37/0.56         (((k2_relat_1 @ (k7_relat_1 @ X3 @ X4)) = (k9_relat_1 @ X3 @ X4))
% 0.37/0.56          | ~ (v1_relat_1 @ X3))),
% 0.37/0.56      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.37/0.56  thf('28', plain,
% 0.37/0.56      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))
% 0.37/0.56        | ~ (v1_relat_1 @ sk_C))),
% 0.37/0.56      inference('sup+', [status(thm)], ['26', '27'])).
% 0.37/0.56  thf('29', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.56      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.56  thf('30', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))),
% 0.37/0.56      inference('demod', [status(thm)], ['28', '29'])).
% 0.37/0.56  thf('31', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(redefinition_k1_relset_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.37/0.56  thf('32', plain,
% 0.37/0.56      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.37/0.56         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.37/0.56          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.37/0.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.37/0.56  thf('33', plain,
% 0.37/0.56      (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.37/0.56      inference('sup-', [status(thm)], ['31', '32'])).
% 0.37/0.56  thf('34', plain,
% 0.37/0.56      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ (k2_relat_1 @ sk_C))
% 0.37/0.56          != (k1_relat_1 @ sk_C)))
% 0.37/0.56         <= (~
% 0.37/0.56             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.37/0.56                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.37/0.56                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.37/0.56      inference('demod', [status(thm)], ['17', '30', '33'])).
% 0.37/0.56  thf('35', plain,
% 0.37/0.56      ((((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 0.37/0.56         <= (~
% 0.37/0.56             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.37/0.56                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.37/0.56                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['14', '34'])).
% 0.37/0.56  thf('36', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.37/0.56      inference('demod', [status(thm)], ['22', '25'])).
% 0.37/0.56  thf('37', plain,
% 0.37/0.56      (![X3 : $i, X4 : $i]:
% 0.37/0.56         (((k2_relat_1 @ (k7_relat_1 @ X3 @ X4)) = (k9_relat_1 @ X3 @ X4))
% 0.37/0.56          | ~ (v1_relat_1 @ X3))),
% 0.37/0.56      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.37/0.56  thf(t169_relat_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( v1_relat_1 @ A ) =>
% 0.37/0.56       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.37/0.56  thf('38', plain,
% 0.37/0.56      (![X5 : $i]:
% 0.37/0.56         (((k10_relat_1 @ X5 @ (k2_relat_1 @ X5)) = (k1_relat_1 @ X5))
% 0.37/0.56          | ~ (v1_relat_1 @ X5))),
% 0.37/0.56      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.37/0.56  thf('39', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.37/0.56            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.37/0.56          | ~ (v1_relat_1 @ X1)
% 0.37/0.56          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['37', '38'])).
% 0.37/0.56  thf('40', plain,
% 0.37/0.56      ((~ (v1_relat_1 @ sk_C)
% 0.37/0.56        | ~ (v1_relat_1 @ sk_C)
% 0.37/0.56        | ((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_B) @ 
% 0.37/0.56            (k9_relat_1 @ sk_C @ sk_B))
% 0.37/0.56            = (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_B))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['36', '39'])).
% 0.37/0.56  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.56      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.56  thf('42', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.56      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.56  thf('43', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.37/0.56      inference('demod', [status(thm)], ['22', '25'])).
% 0.37/0.56  thf('44', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.37/0.56      inference('demod', [status(thm)], ['22', '25'])).
% 0.37/0.56  thf('45', plain,
% 0.37/0.56      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) = (k1_relat_1 @ sk_C))),
% 0.37/0.56      inference('demod', [status(thm)], ['40', '41', '42', '43', '44'])).
% 0.37/0.56  thf('46', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))),
% 0.37/0.56      inference('demod', [status(thm)], ['28', '29'])).
% 0.37/0.56  thf('47', plain,
% 0.37/0.56      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.37/0.56      inference('demod', [status(thm)], ['45', '46'])).
% 0.37/0.56  thf('48', plain,
% 0.37/0.56      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 0.37/0.56         <= (~
% 0.37/0.56             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.37/0.56                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.37/0.56                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.37/0.56      inference('demod', [status(thm)], ['35', '47'])).
% 0.37/0.56  thf('49', plain,
% 0.37/0.56      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.37/0.56          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.37/0.56          = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['48'])).
% 0.37/0.56  thf('50', plain,
% 0.37/0.56      (~
% 0.37/0.56       (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.37/0.56          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.37/0.56          = (k2_relset_1 @ sk_B @ sk_A @ sk_C))) | 
% 0.37/0.56       ~
% 0.37/0.56       (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.37/0.56          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.37/0.56          = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.37/0.56      inference('split', [status(esa)], ['6'])).
% 0.37/0.56  thf('51', plain,
% 0.37/0.56      (~
% 0.37/0.56       (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.37/0.56          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.37/0.56          = (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.37/0.56      inference('sat_resolution*', [status(thm)], ['49', '50'])).
% 0.37/0.56  thf('52', plain,
% 0.37/0.56      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A))
% 0.37/0.56         != (k2_relat_1 @ sk_C))),
% 0.37/0.56      inference('simpl_trail', [status(thm)], ['13', '51'])).
% 0.37/0.56  thf('53', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(t38_relset_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.56       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.37/0.56         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.37/0.56  thf('54', plain,
% 0.37/0.56      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.37/0.56         (((k8_relset_1 @ X29 @ X30 @ X31 @ X30)
% 0.37/0.56            = (k1_relset_1 @ X29 @ X30 @ X31))
% 0.37/0.56          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.37/0.56      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.37/0.56  thf('55', plain,
% 0.37/0.56      (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A)
% 0.37/0.56         = (k1_relset_1 @ sk_B @ sk_A @ sk_C))),
% 0.37/0.56      inference('sup-', [status(thm)], ['53', '54'])).
% 0.37/0.56  thf('56', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.56  thf('57', plain,
% 0.37/0.56      (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.37/0.56      inference('sup-', [status(thm)], ['31', '32'])).
% 0.37/0.56  thf('58', plain, (((k10_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.37/0.56      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.37/0.56  thf(t98_relat_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( v1_relat_1 @ A ) =>
% 0.37/0.56       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.37/0.56  thf('59', plain,
% 0.37/0.56      (![X8 : $i]:
% 0.37/0.56         (((k7_relat_1 @ X8 @ (k1_relat_1 @ X8)) = (X8)) | ~ (v1_relat_1 @ X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.37/0.56  thf('60', plain, ((v4_relat_1 @ sk_C @ sk_B)),
% 0.37/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.56  thf(fc23_relat_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ B ) ) =>
% 0.37/0.56       ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) ) & 
% 0.37/0.56         ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ A ) & 
% 0.37/0.56         ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ))).
% 0.37/0.56  thf('61', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.56         ((v4_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X1)
% 0.37/0.56          | ~ (v4_relat_1 @ X0 @ X2)
% 0.37/0.56          | ~ (v1_relat_1 @ X0))),
% 0.37/0.56      inference('cnf', [status(esa)], [fc23_relat_1])).
% 0.37/0.56  thf('62', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (v1_relat_1 @ sk_C) | (v4_relat_1 @ (k7_relat_1 @ sk_C @ X0) @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['60', '61'])).
% 0.37/0.56  thf('63', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.56      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.56  thf('64', plain, (![X0 : $i]: (v4_relat_1 @ (k7_relat_1 @ sk_C @ X0) @ X0)),
% 0.37/0.56      inference('demod', [status(thm)], ['62', '63'])).
% 0.37/0.56  thf('65', plain,
% 0.37/0.56      (((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) | ~ (v1_relat_1 @ sk_C))),
% 0.37/0.56      inference('sup+', [status(thm)], ['59', '64'])).
% 0.37/0.56  thf('66', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.56      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.56  thf('67', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.37/0.56      inference('demod', [status(thm)], ['65', '66'])).
% 0.37/0.56  thf('68', plain,
% 0.37/0.56      (![X6 : $i, X7 : $i]:
% 0.37/0.56         (((X6) = (k7_relat_1 @ X6 @ X7))
% 0.37/0.56          | ~ (v4_relat_1 @ X6 @ X7)
% 0.37/0.56          | ~ (v1_relat_1 @ X6))),
% 0.37/0.56      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.37/0.56  thf('69', plain,
% 0.37/0.56      ((~ (v1_relat_1 @ sk_C)
% 0.37/0.56        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['67', '68'])).
% 0.37/0.56  thf('70', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.56      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.56  thf('71', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.37/0.56      inference('demod', [status(thm)], ['69', '70'])).
% 0.37/0.56  thf('72', plain,
% 0.37/0.56      (![X3 : $i, X4 : $i]:
% 0.37/0.56         (((k2_relat_1 @ (k7_relat_1 @ X3 @ X4)) = (k9_relat_1 @ X3 @ X4))
% 0.37/0.56          | ~ (v1_relat_1 @ X3))),
% 0.37/0.56      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.37/0.56  thf('73', plain,
% 0.37/0.56      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 0.37/0.56        | ~ (v1_relat_1 @ sk_C))),
% 0.37/0.56      inference('sup+', [status(thm)], ['71', '72'])).
% 0.37/0.56  thf('74', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.56      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.56  thf('75', plain,
% 0.37/0.56      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.37/0.56      inference('demod', [status(thm)], ['73', '74'])).
% 0.37/0.56  thf('76', plain, (((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))),
% 0.37/0.56      inference('demod', [status(thm)], ['52', '58', '75'])).
% 0.37/0.56  thf('77', plain, ($false), inference('simplify', [status(thm)], ['76'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
