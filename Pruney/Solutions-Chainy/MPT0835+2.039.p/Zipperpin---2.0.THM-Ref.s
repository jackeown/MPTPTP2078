%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pY7ZZPEcE4

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 283 expanded)
%              Number of leaves         :   33 (  98 expanded)
%              Depth                    :   15
%              Number of atoms          : 1003 (3776 expanded)
%              Number of equality atoms :   76 ( 219 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf('3',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('7',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( ( k7_relset_1 @ X22 @ X23 @ X21 @ X24 )
        = ( k9_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

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
    ( ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['5','8','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('15',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('16',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('19',plain,(
    v4_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10
        = ( k7_relat_1 @ X10 @ X11 ) )
      | ~ ( v4_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('23',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('25',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['21','26'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('29',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('31',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('33',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('34',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k2_relat_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['16','31','34'])).

thf('36',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','35'])).

thf('37',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('38',plain,(
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

thf('39',plain,(
    ! [X9: $i] :
      ( ( ( k10_relat_1 @ X9 @ ( k2_relat_1 @ X9 ) )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ ( k9_relat_1 @ sk_C @ sk_B ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('43',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('44',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('45',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('46',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['41','42','43','44','45'])).

thf('47',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('48',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['36','48'])).

thf('50',plain,
    ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    = ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('52',plain,(
    ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
 != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['50','51'])).

thf('53',plain,(
    ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['12','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('55',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k8_relset_1 @ X33 @ X34 @ X35 @ X34 )
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('56',plain,
    ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A )
    = ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('58',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('59',plain,
    ( ( k10_relat_1 @ sk_C @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('61',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('63',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X29 ) @ X30 )
      | ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('67',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10
        = ( k7_relat_1 @ X10 @ X11 ) )
      | ~ ( v4_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('69',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('71',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('73',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('75',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['53','59','75'])).

thf('77',plain,(
    $false ),
    inference(simplify,[status(thm)],['76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pY7ZZPEcE4
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:00:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 53 iterations in 0.014s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.46  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.46  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.46  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.46  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.46  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.46  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.46  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(t39_relset_1, conjecture,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.21/0.46       ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.21/0.46           ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.21/0.46         ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.21/0.46           ( k1_relset_1 @ B @ A @ C ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.46        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.21/0.46          ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.21/0.46              ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.21/0.46            ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.21/0.46              ( k1_relset_1 @ B @ A @ C ) ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t39_relset_1])).
% 0.21/0.46  thf('0', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(redefinition_k8_relset_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.46       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.46         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.21/0.46          | ((k8_relset_1 @ X26 @ X27 @ X25 @ X28) = (k10_relat_1 @ X25 @ X28)))),
% 0.21/0.46      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.46          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.46          != (k2_relset_1 @ sk_B @ sk_A @ sk_C))
% 0.21/0.46        | ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.46            (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.46            != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.46          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.46          != (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.21/0.46         <= (~
% 0.21/0.46             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.46                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.46                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.46      inference('split', [status(esa)], ['3'])).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ (k10_relat_1 @ sk_C @ sk_A))
% 0.21/0.46          != (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.21/0.46         <= (~
% 0.21/0.46             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.46                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.46                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['2', '4'])).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(redefinition_k7_relset_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.46       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.46         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.21/0.46          | ((k7_relset_1 @ X22 @ X23 @ X21 @ X24) = (k9_relat_1 @ X21 @ X24)))),
% 0.21/0.46      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.21/0.46  thf('8', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.46  thf('9', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.46       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.46         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 0.21/0.46          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.21/0.46      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.21/0.46      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.46  thf('12', plain,
% 0.21/0.46      ((((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A))
% 0.21/0.46          != (k2_relat_1 @ sk_C)))
% 0.21/0.46         <= (~
% 0.21/0.46             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.46                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.46                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.46      inference('demod', [status(thm)], ['5', '8', '11'])).
% 0.21/0.46  thf('13', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.46  thf('14', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.46  thf('15', plain,
% 0.21/0.46      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.46          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.46          != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.21/0.46         <= (~
% 0.21/0.46             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.46                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.46                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.46      inference('split', [status(esa)], ['3'])).
% 0.21/0.46  thf('16', plain,
% 0.21/0.46      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ (k9_relat_1 @ sk_C @ sk_B))
% 0.21/0.46          != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.21/0.46         <= (~
% 0.21/0.46             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.46                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.46                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.46  thf('17', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(cc2_relset_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.46       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.46  thf('18', plain,
% 0.21/0.46      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.46         ((v4_relat_1 @ X12 @ X13)
% 0.21/0.46          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.21/0.46      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.46  thf('19', plain, ((v4_relat_1 @ sk_C @ sk_B)),
% 0.21/0.46      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.46  thf(t209_relat_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.21/0.46       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.21/0.46  thf('20', plain,
% 0.21/0.46      (![X10 : $i, X11 : $i]:
% 0.21/0.46         (((X10) = (k7_relat_1 @ X10 @ X11))
% 0.21/0.46          | ~ (v4_relat_1 @ X10 @ X11)
% 0.21/0.46          | ~ (v1_relat_1 @ X10))),
% 0.21/0.46      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.21/0.46  thf('21', plain,
% 0.21/0.46      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_B)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.46  thf('22', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(cc2_relat_1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( v1_relat_1 @ A ) =>
% 0.21/0.46       ( ![B:$i]:
% 0.21/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.46  thf('23', plain,
% 0.21/0.46      (![X3 : $i, X4 : $i]:
% 0.21/0.46         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.21/0.46          | (v1_relat_1 @ X3)
% 0.21/0.46          | ~ (v1_relat_1 @ X4))),
% 0.21/0.46      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.46  thf('24', plain,
% 0.21/0.46      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.21/0.46      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.46  thf(fc6_relat_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.46  thf('25', plain,
% 0.21/0.46      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.21/0.46      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.46  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.46      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.46  thf('27', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.21/0.46      inference('demod', [status(thm)], ['21', '26'])).
% 0.21/0.46  thf(t148_relat_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( v1_relat_1 @ B ) =>
% 0.21/0.46       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.21/0.46  thf('28', plain,
% 0.21/0.46      (![X7 : $i, X8 : $i]:
% 0.21/0.46         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 0.21/0.46          | ~ (v1_relat_1 @ X7))),
% 0.21/0.46      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.46  thf('29', plain,
% 0.21/0.46      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))
% 0.21/0.46        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.46      inference('sup+', [status(thm)], ['27', '28'])).
% 0.21/0.46  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.46      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.46  thf('31', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))),
% 0.21/0.46      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.46  thf('32', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.46       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.46  thf('33', plain,
% 0.21/0.46      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.46         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.21/0.46          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.21/0.46      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.46  thf('34', plain,
% 0.21/0.46      (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.21/0.46      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.46  thf('35', plain,
% 0.21/0.46      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ (k2_relat_1 @ sk_C))
% 0.21/0.46          != (k1_relat_1 @ sk_C)))
% 0.21/0.46         <= (~
% 0.21/0.46             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.46                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.46                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.46      inference('demod', [status(thm)], ['16', '31', '34'])).
% 0.21/0.46  thf('36', plain,
% 0.21/0.46      ((((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 0.21/0.46         <= (~
% 0.21/0.46             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.46                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.46                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['13', '35'])).
% 0.21/0.46  thf('37', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.21/0.46      inference('demod', [status(thm)], ['21', '26'])).
% 0.21/0.46  thf('38', plain,
% 0.21/0.46      (![X7 : $i, X8 : $i]:
% 0.21/0.46         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 0.21/0.46          | ~ (v1_relat_1 @ X7))),
% 0.21/0.46      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.46  thf(t169_relat_1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( v1_relat_1 @ A ) =>
% 0.21/0.46       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.21/0.46  thf('39', plain,
% 0.21/0.46      (![X9 : $i]:
% 0.21/0.46         (((k10_relat_1 @ X9 @ (k2_relat_1 @ X9)) = (k1_relat_1 @ X9))
% 0.21/0.46          | ~ (v1_relat_1 @ X9))),
% 0.21/0.46      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.21/0.46  thf('40', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.21/0.46            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.21/0.46          | ~ (v1_relat_1 @ X1)
% 0.21/0.46          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.21/0.46      inference('sup+', [status(thm)], ['38', '39'])).
% 0.21/0.46  thf('41', plain,
% 0.21/0.46      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.46        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.46        | ((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_B) @ 
% 0.21/0.46            (k9_relat_1 @ sk_C @ sk_B))
% 0.21/0.46            = (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_B))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['37', '40'])).
% 0.21/0.46  thf('42', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.46      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.46  thf('43', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.46      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.46  thf('44', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.21/0.46      inference('demod', [status(thm)], ['21', '26'])).
% 0.21/0.46  thf('45', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.21/0.46      inference('demod', [status(thm)], ['21', '26'])).
% 0.21/0.46  thf('46', plain,
% 0.21/0.46      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) = (k1_relat_1 @ sk_C))),
% 0.21/0.46      inference('demod', [status(thm)], ['41', '42', '43', '44', '45'])).
% 0.21/0.46  thf('47', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))),
% 0.21/0.46      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.46  thf('48', plain,
% 0.21/0.46      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.21/0.46      inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.46  thf('49', plain,
% 0.21/0.46      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 0.21/0.46         <= (~
% 0.21/0.46             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.46                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.46                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.46      inference('demod', [status(thm)], ['36', '48'])).
% 0.21/0.46  thf('50', plain,
% 0.21/0.46      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.46          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.46          = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.21/0.46      inference('simplify', [status(thm)], ['49'])).
% 0.21/0.46  thf('51', plain,
% 0.21/0.46      (~
% 0.21/0.46       (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.46          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.46          = (k2_relset_1 @ sk_B @ sk_A @ sk_C))) | 
% 0.21/0.46       ~
% 0.21/0.46       (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.46          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.46          = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.21/0.46      inference('split', [status(esa)], ['3'])).
% 0.21/0.46  thf('52', plain,
% 0.21/0.46      (~
% 0.21/0.46       (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.46          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.46          = (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.21/0.46      inference('sat_resolution*', [status(thm)], ['50', '51'])).
% 0.21/0.46  thf('53', plain,
% 0.21/0.46      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A))
% 0.21/0.46         != (k2_relat_1 @ sk_C))),
% 0.21/0.46      inference('simpl_trail', [status(thm)], ['12', '52'])).
% 0.21/0.46  thf('54', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t38_relset_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.46       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.21/0.46         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.46  thf('55', plain,
% 0.21/0.46      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.21/0.46         (((k8_relset_1 @ X33 @ X34 @ X35 @ X34)
% 0.21/0.46            = (k1_relset_1 @ X33 @ X34 @ X35))
% 0.21/0.46          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.21/0.46      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.21/0.46  thf('56', plain,
% 0.21/0.46      (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A)
% 0.21/0.46         = (k1_relset_1 @ sk_B @ sk_A @ sk_C))),
% 0.21/0.46      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.46  thf('57', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.46  thf('58', plain,
% 0.21/0.46      (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.21/0.46      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.46  thf('59', plain, (((k10_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.21/0.46      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.21/0.46  thf(d10_xboole_0, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.46  thf('60', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.46  thf('61', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.46      inference('simplify', [status(thm)], ['60'])).
% 0.21/0.46  thf('62', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t13_relset_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.21/0.46       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 0.21/0.46         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.21/0.46  thf('63', plain,
% 0.21/0.46      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.21/0.46         (~ (r1_tarski @ (k1_relat_1 @ X29) @ X30)
% 0.21/0.46          | (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.21/0.46          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 0.21/0.46      inference('cnf', [status(esa)], [t13_relset_1])).
% 0.21/0.46  thf('64', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A)))
% 0.21/0.46          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.46  thf('65', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_C @ 
% 0.21/0.46        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_A)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['61', '64'])).
% 0.21/0.46  thf('66', plain,
% 0.21/0.46      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.46         ((v4_relat_1 @ X12 @ X13)
% 0.21/0.46          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.21/0.46      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.46  thf('67', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.21/0.46      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.46  thf('68', plain,
% 0.21/0.46      (![X10 : $i, X11 : $i]:
% 0.21/0.46         (((X10) = (k7_relat_1 @ X10 @ X11))
% 0.21/0.46          | ~ (v4_relat_1 @ X10 @ X11)
% 0.21/0.46          | ~ (v1_relat_1 @ X10))),
% 0.21/0.46      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.21/0.46  thf('69', plain,
% 0.21/0.46      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.46        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.46  thf('70', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.46      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.46  thf('71', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.21/0.46      inference('demod', [status(thm)], ['69', '70'])).
% 0.21/0.46  thf('72', plain,
% 0.21/0.46      (![X7 : $i, X8 : $i]:
% 0.21/0.46         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 0.21/0.46          | ~ (v1_relat_1 @ X7))),
% 0.21/0.46      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.46  thf('73', plain,
% 0.21/0.46      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 0.21/0.46        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.46      inference('sup+', [status(thm)], ['71', '72'])).
% 0.21/0.46  thf('74', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.46      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.46  thf('75', plain,
% 0.21/0.46      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.21/0.46      inference('demod', [status(thm)], ['73', '74'])).
% 0.21/0.46  thf('76', plain, (((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))),
% 0.21/0.46      inference('demod', [status(thm)], ['53', '59', '75'])).
% 0.21/0.46  thf('77', plain, ($false), inference('simplify', [status(thm)], ['76'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
