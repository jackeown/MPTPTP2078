%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eioQ9VxaoA

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:41 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  190 ( 610 expanded)
%              Number of leaves         :   44 ( 215 expanded)
%              Depth                    :   22
%              Number of atoms          : 1531 (6069 expanded)
%              Number of equality atoms :  102 ( 388 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(fc24_relat_1,axiom,(
    ! [A: $i] :
      ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X27: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ X27 ) @ X27 ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

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

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v5_relat_1 @ X33 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('3',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v5_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('10',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['5','10'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('12',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ X29 @ ( k1_relat_1 @ X30 ) )
      | ( r1_tarski @ X29 @ ( k10_relat_1 @ X30 @ ( k9_relat_1 @ X30 @ X29 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ X1 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X32 ) @ ( k6_relat_1 @ X31 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('17',plain,(
    ! [X25: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) )
        = ( k9_relat_1 @ X13 @ ( k2_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X25: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('24',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ X1 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['14','15','25'])).

thf('27',plain,(
    ! [X25: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('28',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k10_relat_1 @ X17 @ X18 )
        = ( k10_relat_1 @ X17 @ ( k3_xboole_0 @ ( k2_relat_1 @ X17 ) @ X18 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ X1 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('33',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','32'])).

thf(t217_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v4_relat_1 @ C @ A ) )
         => ( v4_relat_1 @ C @ B ) ) ) )).

thf('34',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v4_relat_1 @ X21 @ X22 )
      | ( v4_relat_1 @ X21 @ X23 )
      | ~ ( r1_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t217_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_C ) ) )
      | ~ ( v4_relat_1 @ X0 @ ( k2_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ( v4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['0','35'])).

thf('37',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('38',plain,(
    v4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19
        = ( k7_relat_1 @ X19 @ X20 ) )
      | ~ ( v4_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ( ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('42',plain,
    ( ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) )
    = ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('44',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X25: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('47',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('48',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('49',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k10_relat_1 @ X17 @ X18 )
        = ( k10_relat_1 @ X17 @ ( k3_xboole_0 @ ( k2_relat_1 @ X17 ) @ X18 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('50',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_C ) ) )
      = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf('52',plain,
    ( ( k10_relat_1 @ sk_C @ ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_C ) ) )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('53',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X15 @ X16 ) @ ( k1_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('54',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,
    ( ( k10_relat_1 @ sk_C @ ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_C ) ) )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('58',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf('59',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ! [X27: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ X27 ) @ X27 ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('61',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['5','10'])).

thf('62',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v4_relat_1 @ X21 @ X22 )
      | ( v4_relat_1 @ X21 @ X23 )
      | ~ ( r1_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t217_relat_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ sk_B )
      | ~ ( v4_relat_1 @ X0 @ ( k2_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ( v4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('66',plain,(
    v4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19
        = ( k7_relat_1 @ X19 @ X20 ) )
      | ~ ( v4_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ( ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('70',plain,
    ( ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) )
    = ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('72',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X25: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('76',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('77',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['72','73','74','75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('79',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k10_relat_1 @ X17 @ X18 )
        = ( k10_relat_1 @ X17 @ ( k3_xboole_0 @ ( k2_relat_1 @ X17 ) @ X18 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X0 @ X1 )
        = ( k10_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
      = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['77','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf('83',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('85',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ sk_C @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','83','84'])).

thf('86',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['86'])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('89',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k1_relset_1 @ X37 @ X38 @ X36 )
        = ( k1_relat_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('90',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['87','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('93',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( ( k7_relset_1 @ X43 @ X44 @ X42 @ X45 )
        = ( k9_relat_1 @ X42 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['86'])).

thf('96',plain,
    ( ( ( k9_relat_1 @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v4_relat_1 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('99',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19
        = ( k7_relat_1 @ X19 @ X20 ) )
      | ~ ( v4_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('101',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf('103',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('105',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf('107',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('109',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k2_relset_1 @ X40 @ X41 @ X39 )
        = ( k2_relat_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('110',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['96','107','110'])).

thf('112',plain,
    ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['86'])).

thf('114',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
 != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['112','113'])).

thf('115',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['91','114'])).

thf('116',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('117',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( ( k8_relset_1 @ X47 @ X48 @ X46 @ X49 )
        = ( k10_relat_1 @ X46 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ( k10_relat_1 @ sk_C @ sk_B )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['115','118'])).

thf('120',plain,(
    ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ sk_C @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['85','119'])).

thf('121',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('122',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('124',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X50 ) @ X51 )
      | ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['122','125'])).

thf('127',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v4_relat_1 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('128',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19
        = ( k7_relat_1 @ X19 @ X20 ) )
      | ~ ( v4_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('130',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf('132',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('134',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf('136',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['121'])).

thf('138',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ X29 @ ( k1_relat_1 @ X30 ) )
      | ( r1_tarski @ X29 @ ( k10_relat_1 @ X30 @ ( k9_relat_1 @ X30 @ X29 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['136','139'])).

thf('141',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('142',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf('143',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['140','141','142'])).

thf('144',plain,(
    $false ),
    inference(demod,[status(thm)],['120','143'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eioQ9VxaoA
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 19:04:51 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.39/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.57  % Solved by: fo/fo7.sh
% 0.39/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.57  % done 247 iterations in 0.097s
% 0.39/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.57  % SZS output start Refutation
% 0.39/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.57  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.39/0.57  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.39/0.57  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.39/0.57  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.39/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.57  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.39/0.57  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.39/0.57  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.39/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.57  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.39/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.57  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.39/0.57  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.39/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.39/0.57  thf(fc24_relat_1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.39/0.57       ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.39/0.57       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.39/0.57  thf('0', plain, (![X27 : $i]: (v4_relat_1 @ (k6_relat_1 @ X27) @ X27)),
% 0.39/0.57      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.39/0.57  thf(t38_relset_1, conjecture,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.57       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.39/0.57         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.57        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.57          ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.39/0.57            ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) )),
% 0.39/0.57    inference('cnf.neg', [status(esa)], [t38_relset_1])).
% 0.39/0.57  thf('1', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(cc2_relset_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.57       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.39/0.57  thf('2', plain,
% 0.39/0.57      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.39/0.57         ((v5_relat_1 @ X33 @ X35)
% 0.39/0.57          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.39/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.39/0.57  thf('3', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.39/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.57  thf(d19_relat_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ B ) =>
% 0.39/0.57       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.39/0.57  thf('4', plain,
% 0.39/0.57      (![X7 : $i, X8 : $i]:
% 0.39/0.57         (~ (v5_relat_1 @ X7 @ X8)
% 0.39/0.57          | (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 0.39/0.57          | ~ (v1_relat_1 @ X7))),
% 0.39/0.57      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.39/0.57  thf('5', plain,
% 0.39/0.57      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.39/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.39/0.57  thf('6', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(cc2_relat_1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ A ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.39/0.57  thf('7', plain,
% 0.39/0.57      (![X5 : $i, X6 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.39/0.57          | (v1_relat_1 @ X5)
% 0.39/0.57          | ~ (v1_relat_1 @ X6))),
% 0.39/0.57      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.39/0.57  thf('8', plain,
% 0.39/0.57      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.39/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.57  thf(fc6_relat_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.39/0.57  thf('9', plain,
% 0.39/0.57      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.39/0.57  thf('10', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.57      inference('demod', [status(thm)], ['8', '9'])).
% 0.39/0.57  thf('11', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.39/0.57      inference('demod', [status(thm)], ['5', '10'])).
% 0.39/0.57  thf(t71_relat_1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.39/0.57       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.39/0.57  thf('12', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 0.39/0.57      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.39/0.57  thf(t146_funct_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ B ) =>
% 0.39/0.57       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.39/0.57         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.39/0.57  thf('13', plain,
% 0.39/0.57      (![X29 : $i, X30 : $i]:
% 0.39/0.57         (~ (r1_tarski @ X29 @ (k1_relat_1 @ X30))
% 0.39/0.57          | (r1_tarski @ X29 @ (k10_relat_1 @ X30 @ (k9_relat_1 @ X30 @ X29)))
% 0.39/0.57          | ~ (v1_relat_1 @ X30))),
% 0.39/0.57      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.39/0.57  thf('14', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (r1_tarski @ X1 @ X0)
% 0.39/0.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.39/0.57          | (r1_tarski @ X1 @ 
% 0.39/0.57             (k10_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.39/0.57              (k9_relat_1 @ (k6_relat_1 @ X0) @ X1))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['12', '13'])).
% 0.39/0.57  thf('15', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.39/0.57  thf(t43_funct_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.39/0.57       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.39/0.57  thf('16', plain,
% 0.39/0.57      (![X31 : $i, X32 : $i]:
% 0.39/0.57         ((k5_relat_1 @ (k6_relat_1 @ X32) @ (k6_relat_1 @ X31))
% 0.39/0.57           = (k6_relat_1 @ (k3_xboole_0 @ X31 @ X32)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.39/0.57  thf('17', plain, (![X25 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 0.39/0.57      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.39/0.57  thf(t160_relat_1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ A ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( v1_relat_1 @ B ) =>
% 0.39/0.57           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.39/0.57             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.39/0.57  thf('18', plain,
% 0.39/0.57      (![X13 : $i, X14 : $i]:
% 0.39/0.57         (~ (v1_relat_1 @ X13)
% 0.39/0.57          | ((k2_relat_1 @ (k5_relat_1 @ X14 @ X13))
% 0.39/0.57              = (k9_relat_1 @ X13 @ (k2_relat_1 @ X14)))
% 0.39/0.57          | ~ (v1_relat_1 @ X14))),
% 0.39/0.57      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.39/0.57  thf('19', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.39/0.57            = (k9_relat_1 @ X1 @ X0))
% 0.39/0.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.39/0.57          | ~ (v1_relat_1 @ X1))),
% 0.39/0.57      inference('sup+', [status(thm)], ['17', '18'])).
% 0.39/0.57  thf('20', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.39/0.57  thf('21', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.39/0.57            = (k9_relat_1 @ X1 @ X0))
% 0.39/0.57          | ~ (v1_relat_1 @ X1))),
% 0.39/0.57      inference('demod', [status(thm)], ['19', '20'])).
% 0.39/0.57  thf('22', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (((k2_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.39/0.57            = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.39/0.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['16', '21'])).
% 0.39/0.57  thf('23', plain, (![X25 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 0.39/0.57      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.39/0.57  thf('24', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.39/0.57  thf('25', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k3_xboole_0 @ X1 @ X0) = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.39/0.57      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.39/0.57  thf('26', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (r1_tarski @ X1 @ X0)
% 0.39/0.57          | (r1_tarski @ X1 @ 
% 0.39/0.57             (k10_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1))))),
% 0.39/0.57      inference('demod', [status(thm)], ['14', '15', '25'])).
% 0.39/0.57  thf('27', plain, (![X25 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 0.39/0.57      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.39/0.57  thf(t168_relat_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ B ) =>
% 0.39/0.57       ( ( k10_relat_1 @ B @ A ) =
% 0.39/0.57         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 0.39/0.57  thf('28', plain,
% 0.39/0.57      (![X17 : $i, X18 : $i]:
% 0.39/0.57         (((k10_relat_1 @ X17 @ X18)
% 0.39/0.57            = (k10_relat_1 @ X17 @ (k3_xboole_0 @ (k2_relat_1 @ X17) @ X18)))
% 0.39/0.57          | ~ (v1_relat_1 @ X17))),
% 0.39/0.57      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.39/0.57  thf('29', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.39/0.57            = (k10_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 0.39/0.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['27', '28'])).
% 0.39/0.57  thf('30', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.39/0.57  thf('31', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k10_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.39/0.57           = (k10_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.39/0.57      inference('demod', [status(thm)], ['29', '30'])).
% 0.39/0.57  thf('32', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (r1_tarski @ X1 @ X0)
% 0.39/0.57          | (r1_tarski @ X1 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.39/0.57      inference('demod', [status(thm)], ['26', '31'])).
% 0.39/0.57  thf('33', plain,
% 0.39/0.57      ((r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.39/0.57        (k10_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_relat_1 @ sk_C)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['11', '32'])).
% 0.39/0.57  thf(t217_relat_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( r1_tarski @ A @ B ) =>
% 0.39/0.57       ( ![C:$i]:
% 0.39/0.57         ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ A ) ) =>
% 0.39/0.57           ( v4_relat_1 @ C @ B ) ) ) ))).
% 0.39/0.57  thf('34', plain,
% 0.39/0.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.39/0.57         (~ (v1_relat_1 @ X21)
% 0.39/0.57          | ~ (v4_relat_1 @ X21 @ X22)
% 0.39/0.57          | (v4_relat_1 @ X21 @ X23)
% 0.39/0.57          | ~ (r1_tarski @ X22 @ X23))),
% 0.39/0.57      inference('cnf', [status(esa)], [t217_relat_1])).
% 0.39/0.57  thf('35', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v4_relat_1 @ X0 @ 
% 0.39/0.57           (k10_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_relat_1 @ sk_C)))
% 0.39/0.57          | ~ (v4_relat_1 @ X0 @ (k2_relat_1 @ sk_C))
% 0.39/0.57          | ~ (v1_relat_1 @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['33', '34'])).
% 0.39/0.57  thf('36', plain,
% 0.39/0.57      ((~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.39/0.57        | (v4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ 
% 0.39/0.57           (k10_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_relat_1 @ sk_C))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['0', '35'])).
% 0.39/0.57  thf('37', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.39/0.57  thf('38', plain,
% 0.39/0.57      ((v4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ 
% 0.39/0.57        (k10_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_relat_1 @ sk_C)))),
% 0.39/0.57      inference('demod', [status(thm)], ['36', '37'])).
% 0.39/0.57  thf(t209_relat_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.39/0.57       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.39/0.57  thf('39', plain,
% 0.39/0.57      (![X19 : $i, X20 : $i]:
% 0.39/0.57         (((X19) = (k7_relat_1 @ X19 @ X20))
% 0.39/0.57          | ~ (v4_relat_1 @ X19 @ X20)
% 0.39/0.57          | ~ (v1_relat_1 @ X19))),
% 0.39/0.57      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.39/0.57  thf('40', plain,
% 0.39/0.57      ((~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.39/0.57        | ((k6_relat_1 @ (k2_relat_1 @ sk_C))
% 0.39/0.57            = (k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ 
% 0.39/0.57               (k10_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_relat_1 @ sk_C)))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['38', '39'])).
% 0.39/0.57  thf('41', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.39/0.57  thf('42', plain,
% 0.39/0.57      (((k6_relat_1 @ (k2_relat_1 @ sk_C))
% 0.39/0.57         = (k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ 
% 0.39/0.57            (k10_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_relat_1 @ sk_C))))),
% 0.39/0.57      inference('demod', [status(thm)], ['40', '41'])).
% 0.39/0.57  thf(t148_relat_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ B ) =>
% 0.39/0.57       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.39/0.57  thf('43', plain,
% 0.39/0.57      (![X11 : $i, X12 : $i]:
% 0.39/0.57         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.39/0.57          | ~ (v1_relat_1 @ X11))),
% 0.39/0.57      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.39/0.57  thf('44', plain,
% 0.39/0.57      ((((k2_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.39/0.57          = (k9_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ 
% 0.39/0.57             (k10_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_relat_1 @ sk_C))))
% 0.39/0.57        | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C))))),
% 0.39/0.57      inference('sup+', [status(thm)], ['42', '43'])).
% 0.39/0.57  thf('45', plain, (![X25 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 0.39/0.57      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.39/0.57  thf('46', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k3_xboole_0 @ X1 @ X0) = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.39/0.57      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.39/0.57  thf('47', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.39/0.57  thf('48', plain,
% 0.39/0.57      (((k2_relat_1 @ sk_C)
% 0.39/0.57         = (k3_xboole_0 @ (k2_relat_1 @ sk_C) @ 
% 0.39/0.57            (k10_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_relat_1 @ sk_C))))),
% 0.39/0.57      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 0.39/0.57  thf('49', plain,
% 0.39/0.57      (![X17 : $i, X18 : $i]:
% 0.39/0.57         (((k10_relat_1 @ X17 @ X18)
% 0.39/0.57            = (k10_relat_1 @ X17 @ (k3_xboole_0 @ (k2_relat_1 @ X17) @ X18)))
% 0.39/0.57          | ~ (v1_relat_1 @ X17))),
% 0.39/0.57      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.39/0.57  thf('50', plain,
% 0.39/0.57      ((((k10_relat_1 @ sk_C @ 
% 0.39/0.57          (k10_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_relat_1 @ sk_C)))
% 0.39/0.57          = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.39/0.57        | ~ (v1_relat_1 @ sk_C))),
% 0.39/0.57      inference('sup+', [status(thm)], ['48', '49'])).
% 0.39/0.57  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.57      inference('demod', [status(thm)], ['8', '9'])).
% 0.39/0.57  thf('52', plain,
% 0.39/0.57      (((k10_relat_1 @ sk_C @ 
% 0.39/0.57         (k10_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_relat_1 @ sk_C)))
% 0.39/0.57         = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 0.39/0.57      inference('demod', [status(thm)], ['50', '51'])).
% 0.39/0.57  thf(t167_relat_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ B ) =>
% 0.39/0.57       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.39/0.57  thf('53', plain,
% 0.39/0.57      (![X15 : $i, X16 : $i]:
% 0.39/0.57         ((r1_tarski @ (k10_relat_1 @ X15 @ X16) @ (k1_relat_1 @ X15))
% 0.39/0.57          | ~ (v1_relat_1 @ X15))),
% 0.39/0.57      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.39/0.57  thf(d10_xboole_0, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.57  thf('54', plain,
% 0.39/0.57      (![X2 : $i, X4 : $i]:
% 0.39/0.57         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.39/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.57  thf('55', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (v1_relat_1 @ X0)
% 0.39/0.57          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.39/0.57          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['53', '54'])).
% 0.39/0.57  thf('56', plain,
% 0.39/0.57      ((~ (r1_tarski @ (k1_relat_1 @ sk_C) @ 
% 0.39/0.57           (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.39/0.57        | ((k1_relat_1 @ sk_C)
% 0.39/0.57            = (k10_relat_1 @ sk_C @ 
% 0.39/0.57               (k10_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_relat_1 @ sk_C))))
% 0.39/0.57        | ~ (v1_relat_1 @ sk_C))),
% 0.39/0.57      inference('sup-', [status(thm)], ['52', '55'])).
% 0.39/0.57  thf('57', plain,
% 0.39/0.57      (((k10_relat_1 @ sk_C @ 
% 0.39/0.57         (k10_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_relat_1 @ sk_C)))
% 0.39/0.57         = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 0.39/0.57      inference('demod', [status(thm)], ['50', '51'])).
% 0.39/0.57  thf('58', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.57      inference('demod', [status(thm)], ['8', '9'])).
% 0.39/0.57  thf('59', plain,
% 0.39/0.57      ((~ (r1_tarski @ (k1_relat_1 @ sk_C) @ 
% 0.39/0.57           (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.39/0.57        | ((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C))))),
% 0.39/0.57      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.39/0.57  thf('60', plain, (![X27 : $i]: (v4_relat_1 @ (k6_relat_1 @ X27) @ X27)),
% 0.39/0.57      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.39/0.57  thf('61', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.39/0.57      inference('demod', [status(thm)], ['5', '10'])).
% 0.39/0.57  thf('62', plain,
% 0.39/0.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.39/0.57         (~ (v1_relat_1 @ X21)
% 0.39/0.57          | ~ (v4_relat_1 @ X21 @ X22)
% 0.39/0.57          | (v4_relat_1 @ X21 @ X23)
% 0.39/0.57          | ~ (r1_tarski @ X22 @ X23))),
% 0.39/0.57      inference('cnf', [status(esa)], [t217_relat_1])).
% 0.39/0.57  thf('63', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v4_relat_1 @ X0 @ sk_B)
% 0.39/0.57          | ~ (v4_relat_1 @ X0 @ (k2_relat_1 @ sk_C))
% 0.39/0.57          | ~ (v1_relat_1 @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['61', '62'])).
% 0.39/0.57  thf('64', plain,
% 0.39/0.57      ((~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.39/0.57        | (v4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ sk_B))),
% 0.39/0.57      inference('sup-', [status(thm)], ['60', '63'])).
% 0.39/0.57  thf('65', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.39/0.57  thf('66', plain, ((v4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ sk_B)),
% 0.39/0.57      inference('demod', [status(thm)], ['64', '65'])).
% 0.39/0.57  thf('67', plain,
% 0.39/0.57      (![X19 : $i, X20 : $i]:
% 0.39/0.57         (((X19) = (k7_relat_1 @ X19 @ X20))
% 0.39/0.57          | ~ (v4_relat_1 @ X19 @ X20)
% 0.39/0.57          | ~ (v1_relat_1 @ X19))),
% 0.39/0.57      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.39/0.57  thf('68', plain,
% 0.39/0.57      ((~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.39/0.57        | ((k6_relat_1 @ (k2_relat_1 @ sk_C))
% 0.39/0.57            = (k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ sk_B)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['66', '67'])).
% 0.39/0.57  thf('69', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.39/0.57  thf('70', plain,
% 0.39/0.57      (((k6_relat_1 @ (k2_relat_1 @ sk_C))
% 0.39/0.57         = (k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ sk_B))),
% 0.39/0.57      inference('demod', [status(thm)], ['68', '69'])).
% 0.39/0.57  thf('71', plain,
% 0.39/0.57      (![X11 : $i, X12 : $i]:
% 0.39/0.57         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.39/0.57          | ~ (v1_relat_1 @ X11))),
% 0.39/0.57      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.39/0.57  thf('72', plain,
% 0.39/0.57      ((((k2_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.39/0.57          = (k9_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ sk_B))
% 0.39/0.57        | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C))))),
% 0.39/0.57      inference('sup+', [status(thm)], ['70', '71'])).
% 0.39/0.57  thf('73', plain, (![X25 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 0.39/0.57      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.39/0.57  thf('74', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k3_xboole_0 @ X1 @ X0) = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.39/0.57      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.39/0.57  thf(commutativity_k3_xboole_0, axiom,
% 0.39/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.39/0.57  thf('75', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.57  thf('76', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.39/0.57  thf('77', plain,
% 0.39/0.57      (((k2_relat_1 @ sk_C) = (k3_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C)))),
% 0.39/0.57      inference('demod', [status(thm)], ['72', '73', '74', '75', '76'])).
% 0.39/0.57  thf('78', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.57  thf('79', plain,
% 0.39/0.57      (![X17 : $i, X18 : $i]:
% 0.39/0.57         (((k10_relat_1 @ X17 @ X18)
% 0.39/0.57            = (k10_relat_1 @ X17 @ (k3_xboole_0 @ (k2_relat_1 @ X17) @ X18)))
% 0.39/0.57          | ~ (v1_relat_1 @ X17))),
% 0.39/0.57      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.39/0.57  thf('80', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (((k10_relat_1 @ X0 @ X1)
% 0.39/0.57            = (k10_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0))))
% 0.39/0.57          | ~ (v1_relat_1 @ X0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['78', '79'])).
% 0.39/0.57  thf('81', plain,
% 0.39/0.57      ((((k10_relat_1 @ sk_C @ sk_B)
% 0.39/0.57          = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.39/0.57        | ~ (v1_relat_1 @ sk_C))),
% 0.39/0.57      inference('sup+', [status(thm)], ['77', '80'])).
% 0.39/0.57  thf('82', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.57      inference('demod', [status(thm)], ['8', '9'])).
% 0.39/0.57  thf('83', plain,
% 0.39/0.57      (((k10_relat_1 @ sk_C @ sk_B)
% 0.39/0.57         = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 0.39/0.57      inference('demod', [status(thm)], ['81', '82'])).
% 0.39/0.57  thf('84', plain,
% 0.39/0.57      (((k10_relat_1 @ sk_C @ sk_B)
% 0.39/0.57         = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 0.39/0.57      inference('demod', [status(thm)], ['81', '82'])).
% 0.39/0.57  thf('85', plain,
% 0.39/0.57      ((~ (r1_tarski @ (k1_relat_1 @ sk_C) @ (k10_relat_1 @ sk_C @ sk_B))
% 0.39/0.57        | ((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_B)))),
% 0.39/0.57      inference('demod', [status(thm)], ['59', '83', '84'])).
% 0.39/0.57  thf('86', plain,
% 0.39/0.57      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.39/0.57          != (k2_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.39/0.57        | ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.39/0.57            != (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('87', plain,
% 0.39/0.57      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.39/0.57          != (k1_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.39/0.57         <= (~
% 0.39/0.57             (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.39/0.57                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.39/0.57      inference('split', [status(esa)], ['86'])).
% 0.39/0.57  thf('88', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(redefinition_k1_relset_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.57       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.39/0.57  thf('89', plain,
% 0.39/0.57      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.39/0.57         (((k1_relset_1 @ X37 @ X38 @ X36) = (k1_relat_1 @ X36))
% 0.39/0.57          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.39/0.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.39/0.57  thf('90', plain,
% 0.39/0.57      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.39/0.57      inference('sup-', [status(thm)], ['88', '89'])).
% 0.39/0.57  thf('91', plain,
% 0.39/0.57      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B) != (k1_relat_1 @ sk_C)))
% 0.39/0.57         <= (~
% 0.39/0.57             (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.39/0.57                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.39/0.57      inference('demod', [status(thm)], ['87', '90'])).
% 0.39/0.57  thf('92', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(redefinition_k7_relset_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.57       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.39/0.57  thf('93', plain,
% 0.39/0.57      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 0.39/0.57          | ((k7_relset_1 @ X43 @ X44 @ X42 @ X45) = (k9_relat_1 @ X42 @ X45)))),
% 0.39/0.57      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.39/0.57  thf('94', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['92', '93'])).
% 0.39/0.57  thf('95', plain,
% 0.39/0.57      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.39/0.57          != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.39/0.57         <= (~
% 0.39/0.57             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.39/0.57                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.39/0.57      inference('split', [status(esa)], ['86'])).
% 0.39/0.57  thf('96', plain,
% 0.39/0.57      ((((k9_relat_1 @ sk_C @ sk_A) != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.39/0.57         <= (~
% 0.39/0.57             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.39/0.57                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['94', '95'])).
% 0.39/0.57  thf('97', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('98', plain,
% 0.39/0.57      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.39/0.57         ((v4_relat_1 @ X33 @ X34)
% 0.39/0.57          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.39/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.39/0.57  thf('99', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.39/0.57      inference('sup-', [status(thm)], ['97', '98'])).
% 0.39/0.57  thf('100', plain,
% 0.39/0.57      (![X19 : $i, X20 : $i]:
% 0.39/0.57         (((X19) = (k7_relat_1 @ X19 @ X20))
% 0.39/0.57          | ~ (v4_relat_1 @ X19 @ X20)
% 0.39/0.57          | ~ (v1_relat_1 @ X19))),
% 0.39/0.57      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.39/0.57  thf('101', plain,
% 0.39/0.57      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['99', '100'])).
% 0.39/0.57  thf('102', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.57      inference('demod', [status(thm)], ['8', '9'])).
% 0.39/0.57  thf('103', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.39/0.57      inference('demod', [status(thm)], ['101', '102'])).
% 0.39/0.57  thf('104', plain,
% 0.39/0.57      (![X11 : $i, X12 : $i]:
% 0.39/0.57         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.39/0.57          | ~ (v1_relat_1 @ X11))),
% 0.39/0.57      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.39/0.57  thf('105', plain,
% 0.39/0.57      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))
% 0.39/0.57        | ~ (v1_relat_1 @ sk_C))),
% 0.39/0.57      inference('sup+', [status(thm)], ['103', '104'])).
% 0.39/0.57  thf('106', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.57      inference('demod', [status(thm)], ['8', '9'])).
% 0.39/0.57  thf('107', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.39/0.57      inference('demod', [status(thm)], ['105', '106'])).
% 0.39/0.57  thf('108', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(redefinition_k2_relset_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.57       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.39/0.57  thf('109', plain,
% 0.39/0.57      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.39/0.57         (((k2_relset_1 @ X40 @ X41 @ X39) = (k2_relat_1 @ X39))
% 0.39/0.57          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 0.39/0.57      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.39/0.57  thf('110', plain,
% 0.39/0.57      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.39/0.57      inference('sup-', [status(thm)], ['108', '109'])).
% 0.39/0.57  thf('111', plain,
% 0.39/0.57      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.39/0.57         <= (~
% 0.39/0.57             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.39/0.57                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.39/0.57      inference('demod', [status(thm)], ['96', '107', '110'])).
% 0.39/0.57  thf('112', plain,
% 0.39/0.57      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.39/0.57          = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.57      inference('simplify', [status(thm)], ['111'])).
% 0.39/0.57  thf('113', plain,
% 0.39/0.57      (~
% 0.39/0.57       (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.39/0.57          = (k1_relset_1 @ sk_A @ sk_B @ sk_C))) | 
% 0.39/0.57       ~
% 0.39/0.57       (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.39/0.57          = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.57      inference('split', [status(esa)], ['86'])).
% 0.39/0.57  thf('114', plain,
% 0.39/0.57      (~
% 0.39/0.57       (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.39/0.57          = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.57      inference('sat_resolution*', [status(thm)], ['112', '113'])).
% 0.39/0.57  thf('115', plain,
% 0.39/0.57      (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B) != (k1_relat_1 @ sk_C))),
% 0.39/0.57      inference('simpl_trail', [status(thm)], ['91', '114'])).
% 0.39/0.57  thf('116', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(redefinition_k8_relset_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.57       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.39/0.57  thf('117', plain,
% 0.39/0.57      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 0.39/0.57          | ((k8_relset_1 @ X47 @ X48 @ X46 @ X49) = (k10_relat_1 @ X46 @ X49)))),
% 0.39/0.57      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.39/0.57  thf('118', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['116', '117'])).
% 0.39/0.57  thf('119', plain, (((k10_relat_1 @ sk_C @ sk_B) != (k1_relat_1 @ sk_C))),
% 0.39/0.57      inference('demod', [status(thm)], ['115', '118'])).
% 0.39/0.57  thf('120', plain,
% 0.39/0.57      (~ (r1_tarski @ (k1_relat_1 @ sk_C) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.39/0.57      inference('simplify_reflect-', [status(thm)], ['85', '119'])).
% 0.39/0.57  thf('121', plain,
% 0.39/0.57      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.57  thf('122', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.39/0.57      inference('simplify', [status(thm)], ['121'])).
% 0.39/0.57  thf('123', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(t13_relset_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.39/0.57       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 0.39/0.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.39/0.57  thf('124', plain,
% 0.39/0.57      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.39/0.57         (~ (r1_tarski @ (k1_relat_1 @ X50) @ X51)
% 0.39/0.57          | (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 0.39/0.57          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X52))))),
% 0.39/0.57      inference('cnf', [status(esa)], [t13_relset_1])).
% 0.39/0.57  thf('125', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.39/0.57          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['123', '124'])).
% 0.39/0.57  thf('126', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_C @ 
% 0.39/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['122', '125'])).
% 0.39/0.57  thf('127', plain,
% 0.39/0.57      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.39/0.57         ((v4_relat_1 @ X33 @ X34)
% 0.39/0.57          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.39/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.39/0.57  thf('128', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.39/0.57      inference('sup-', [status(thm)], ['126', '127'])).
% 0.39/0.57  thf('129', plain,
% 0.39/0.57      (![X19 : $i, X20 : $i]:
% 0.39/0.57         (((X19) = (k7_relat_1 @ X19 @ X20))
% 0.39/0.57          | ~ (v4_relat_1 @ X19 @ X20)
% 0.39/0.57          | ~ (v1_relat_1 @ X19))),
% 0.39/0.57      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.39/0.57  thf('130', plain,
% 0.39/0.57      ((~ (v1_relat_1 @ sk_C)
% 0.39/0.57        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['128', '129'])).
% 0.39/0.57  thf('131', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.57      inference('demod', [status(thm)], ['8', '9'])).
% 0.39/0.57  thf('132', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.39/0.57      inference('demod', [status(thm)], ['130', '131'])).
% 0.39/0.57  thf('133', plain,
% 0.39/0.57      (![X11 : $i, X12 : $i]:
% 0.39/0.57         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.39/0.57          | ~ (v1_relat_1 @ X11))),
% 0.39/0.57      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.39/0.57  thf('134', plain,
% 0.39/0.57      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 0.39/0.57        | ~ (v1_relat_1 @ sk_C))),
% 0.39/0.57      inference('sup+', [status(thm)], ['132', '133'])).
% 0.39/0.57  thf('135', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.57      inference('demod', [status(thm)], ['8', '9'])).
% 0.39/0.57  thf('136', plain,
% 0.39/0.57      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.39/0.57      inference('demod', [status(thm)], ['134', '135'])).
% 0.39/0.57  thf('137', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.39/0.57      inference('simplify', [status(thm)], ['121'])).
% 0.39/0.57  thf('138', plain,
% 0.39/0.57      (![X29 : $i, X30 : $i]:
% 0.39/0.57         (~ (r1_tarski @ X29 @ (k1_relat_1 @ X30))
% 0.39/0.57          | (r1_tarski @ X29 @ (k10_relat_1 @ X30 @ (k9_relat_1 @ X30 @ X29)))
% 0.39/0.57          | ~ (v1_relat_1 @ X30))),
% 0.39/0.57      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.39/0.57  thf('139', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (v1_relat_1 @ X0)
% 0.39/0.57          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.39/0.57             (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['137', '138'])).
% 0.39/0.57  thf('140', plain,
% 0.39/0.57      (((r1_tarski @ (k1_relat_1 @ sk_C) @ 
% 0.39/0.57         (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.39/0.57        | ~ (v1_relat_1 @ sk_C))),
% 0.39/0.57      inference('sup+', [status(thm)], ['136', '139'])).
% 0.39/0.57  thf('141', plain,
% 0.39/0.57      (((k10_relat_1 @ sk_C @ sk_B)
% 0.39/0.57         = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 0.39/0.57      inference('demod', [status(thm)], ['81', '82'])).
% 0.39/0.57  thf('142', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.57      inference('demod', [status(thm)], ['8', '9'])).
% 0.39/0.57  thf('143', plain,
% 0.39/0.57      ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.39/0.57      inference('demod', [status(thm)], ['140', '141', '142'])).
% 0.39/0.57  thf('144', plain, ($false), inference('demod', [status(thm)], ['120', '143'])).
% 0.39/0.57  
% 0.39/0.57  % SZS output end Refutation
% 0.39/0.57  
% 0.39/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
