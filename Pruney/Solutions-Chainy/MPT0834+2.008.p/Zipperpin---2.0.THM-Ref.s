%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pETNF7tW2x

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:39 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 543 expanded)
%              Number of leaves         :   44 ( 187 expanded)
%              Depth                    :   23
%              Number of atoms          : 1391 (5677 expanded)
%              Number of equality atoms :   94 ( 351 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ X31 @ ( k1_relat_1 @ X32 ) )
      | ( r1_tarski @ X31 @ ( k10_relat_1 @ X32 @ ( k9_relat_1 @ X32 @ X31 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k10_relat_1 @ X15 @ X16 )
        = ( k10_relat_1 @ X15 @ ( k3_xboole_0 @ ( k2_relat_1 @ X15 ) @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf(fc24_relat_1,axiom,(
    ! [A: $i] :
      ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X29: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ X29 ) @ X29 ) ),
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

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( v4_relat_1 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('8',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17
        = ( k7_relat_1 @ X17 @ X18 ) )
      | ~ ( v4_relat_1 @ X17 @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('12',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( v1_relat_1 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('13',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['10','13'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('15',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X24 @ X25 ) ) @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('16',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('18',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['16','17'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('19',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X13 @ X14 ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('20',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t217_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v4_relat_1 @ C @ A ) )
         => ( v4_relat_1 @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v4_relat_1 @ X19 @ X20 )
      | ( v4_relat_1 @ X19 @ X21 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t217_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_relat_1 @ X1 @ sk_A )
      | ~ ( v4_relat_1 @ X1 @ ( k10_relat_1 @ sk_C @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_C @ X0 ) ) )
      | ( v4_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_C @ X0 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','26'])).

thf('28',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_C @ X0 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17
        = ( k7_relat_1 @ X17 @ X18 ) )
      | ~ ( v4_relat_1 @ X17 @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_C @ X0 ) ) )
      | ( ( k6_relat_1 @ ( k10_relat_1 @ sk_C @ X0 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_C @ X0 ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k6_relat_1 @ ( k10_relat_1 @ sk_C @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_C @ X0 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_C @ X0 ) ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_C @ X0 ) ) @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('36',plain,(
    ! [X23: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('37',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('38',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X34 ) @ ( k6_relat_1 @ X33 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('39',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k7_relat_1 @ X27 @ X26 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X26 ) @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X23: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['37','44'])).

thf('46',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C @ X0 )
      = ( k3_xboole_0 @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36','47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['4','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C @ X0 )
      = ( k3_xboole_0 @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36','47','48'])).

thf('52',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X13 @ X14 ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('55',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ sk_C @ X0 ) )
      | ( ( k1_relat_1 @ sk_C )
        = ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('59',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ sk_C @ X0 ) )
      | ( ( k1_relat_1 @ sk_C )
        = ( k10_relat_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['3','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('63',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('65',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X55 ) @ X56 )
      | ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X57 ) ) )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X57 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( v4_relat_1 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('69',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17
        = ( k7_relat_1 @ X17 @ X18 ) )
      | ~ ( v4_relat_1 @ X17 @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('71',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('73',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('75',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('77',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X29: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ X29 ) @ X29 ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( v5_relat_1 @ X38 @ X40 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('81',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['79','80'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('82',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v5_relat_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('83',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('85',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v4_relat_1 @ X19 @ X20 )
      | ( v4_relat_1 @ X19 @ X21 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t217_relat_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ sk_B )
      | ~ ( v4_relat_1 @ X0 @ ( k2_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ( v4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['78','87'])).

thf('89',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('90',plain,(
    v4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17
        = ( k7_relat_1 @ X17 @ X18 ) )
      | ~ ( v4_relat_1 @ X17 @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('92',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ( ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('94',plain,
    ( ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) )
    = ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('96',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    = ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup+',[status(thm)],['94','97'])).

thf('99',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('100',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k10_relat_1 @ X15 @ X16 )
        = ( k10_relat_1 @ X15 @ ( k3_xboole_0 @ ( k2_relat_1 @ X15 ) @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('102',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
      = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('104',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['61','62','77','104'])).

thf('106',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['106'])).

thf('108',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('109',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) )
      | ( ( k8_relset_1 @ X52 @ X53 @ X51 @ X54 )
        = ( k10_relat_1 @ X51 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('112',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( ( k1_relset_1 @ X42 @ X43 @ X41 )
        = ( k1_relat_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('113',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['107','110','113'])).

thf('115',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('116',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ( ( k7_relset_1 @ X48 @ X49 @ X47 @ X50 )
        = ( k9_relat_1 @ X47 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['106'])).

thf('119',plain,
    ( ( ( k9_relat_1 @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('121',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('122',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('124',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('126',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( ( k2_relset_1 @ X45 @ X46 @ X44 )
        = ( k2_relat_1 @ X44 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('127',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['119','124','127'])).

thf('129',plain,
    ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['106'])).

thf('131',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
 != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['129','130'])).

thf('132',plain,(
    ( k10_relat_1 @ sk_C @ sk_B )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['114','131'])).

thf('133',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['105','132'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pETNF7tW2x
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:38:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 1.19/1.37  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.19/1.37  % Solved by: fo/fo7.sh
% 1.19/1.37  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.19/1.37  % done 1474 iterations in 0.917s
% 1.19/1.37  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.19/1.37  % SZS output start Refutation
% 1.19/1.37  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.19/1.37  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.19/1.37  thf(sk_B_type, type, sk_B: $i).
% 1.19/1.37  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.19/1.37  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.19/1.37  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.19/1.37  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.19/1.37  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.19/1.37  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.19/1.37  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.19/1.37  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 1.19/1.37  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.19/1.37  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.19/1.37  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.19/1.37  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.19/1.37  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.19/1.37  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.19/1.37  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.19/1.37  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.19/1.37  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.19/1.37  thf(sk_C_type, type, sk_C: $i).
% 1.19/1.37  thf(sk_A_type, type, sk_A: $i).
% 1.19/1.37  thf(d10_xboole_0, axiom,
% 1.19/1.37    (![A:$i,B:$i]:
% 1.19/1.37     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.19/1.37  thf('0', plain,
% 1.19/1.37      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.19/1.37      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.19/1.37  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.19/1.37      inference('simplify', [status(thm)], ['0'])).
% 1.19/1.37  thf(t146_funct_1, axiom,
% 1.19/1.37    (![A:$i,B:$i]:
% 1.19/1.37     ( ( v1_relat_1 @ B ) =>
% 1.19/1.37       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 1.19/1.37         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 1.19/1.37  thf('2', plain,
% 1.19/1.37      (![X31 : $i, X32 : $i]:
% 1.19/1.37         (~ (r1_tarski @ X31 @ (k1_relat_1 @ X32))
% 1.19/1.37          | (r1_tarski @ X31 @ (k10_relat_1 @ X32 @ (k9_relat_1 @ X32 @ X31)))
% 1.19/1.37          | ~ (v1_relat_1 @ X32))),
% 1.19/1.37      inference('cnf', [status(esa)], [t146_funct_1])).
% 1.19/1.37  thf('3', plain,
% 1.19/1.37      (![X0 : $i]:
% 1.19/1.37         (~ (v1_relat_1 @ X0)
% 1.19/1.37          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 1.19/1.37             (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 1.19/1.37      inference('sup-', [status(thm)], ['1', '2'])).
% 1.19/1.37  thf(t168_relat_1, axiom,
% 1.19/1.37    (![A:$i,B:$i]:
% 1.19/1.37     ( ( v1_relat_1 @ B ) =>
% 1.19/1.37       ( ( k10_relat_1 @ B @ A ) =
% 1.19/1.37         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 1.19/1.37  thf('4', plain,
% 1.19/1.37      (![X15 : $i, X16 : $i]:
% 1.19/1.37         (((k10_relat_1 @ X15 @ X16)
% 1.19/1.37            = (k10_relat_1 @ X15 @ (k3_xboole_0 @ (k2_relat_1 @ X15) @ X16)))
% 1.19/1.37          | ~ (v1_relat_1 @ X15))),
% 1.19/1.37      inference('cnf', [status(esa)], [t168_relat_1])).
% 1.19/1.37  thf(fc24_relat_1, axiom,
% 1.19/1.37    (![A:$i]:
% 1.19/1.37     ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 1.19/1.37       ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 1.19/1.37       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.19/1.37  thf('5', plain, (![X29 : $i]: (v4_relat_1 @ (k6_relat_1 @ X29) @ X29)),
% 1.19/1.37      inference('cnf', [status(esa)], [fc24_relat_1])).
% 1.19/1.37  thf(t38_relset_1, conjecture,
% 1.19/1.37    (![A:$i,B:$i,C:$i]:
% 1.19/1.37     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.19/1.37       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 1.19/1.37         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.19/1.37  thf(zf_stmt_0, negated_conjecture,
% 1.19/1.37    (~( ![A:$i,B:$i,C:$i]:
% 1.19/1.37        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.19/1.37          ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 1.19/1.37            ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) )),
% 1.19/1.37    inference('cnf.neg', [status(esa)], [t38_relset_1])).
% 1.19/1.37  thf('6', plain,
% 1.19/1.37      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf(cc2_relset_1, axiom,
% 1.19/1.37    (![A:$i,B:$i,C:$i]:
% 1.19/1.37     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.19/1.37       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.19/1.37  thf('7', plain,
% 1.19/1.37      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.19/1.37         ((v4_relat_1 @ X38 @ X39)
% 1.19/1.37          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 1.19/1.37      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.19/1.37  thf('8', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 1.19/1.37      inference('sup-', [status(thm)], ['6', '7'])).
% 1.19/1.37  thf(t209_relat_1, axiom,
% 1.19/1.37    (![A:$i,B:$i]:
% 1.19/1.37     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.19/1.37       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 1.19/1.37  thf('9', plain,
% 1.19/1.37      (![X17 : $i, X18 : $i]:
% 1.19/1.37         (((X17) = (k7_relat_1 @ X17 @ X18))
% 1.19/1.37          | ~ (v4_relat_1 @ X17 @ X18)
% 1.19/1.37          | ~ (v1_relat_1 @ X17))),
% 1.19/1.37      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.19/1.37  thf('10', plain,
% 1.19/1.37      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 1.19/1.37      inference('sup-', [status(thm)], ['8', '9'])).
% 1.19/1.37  thf('11', plain,
% 1.19/1.37      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf(cc1_relset_1, axiom,
% 1.19/1.37    (![A:$i,B:$i,C:$i]:
% 1.19/1.37     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.19/1.37       ( v1_relat_1 @ C ) ))).
% 1.19/1.37  thf('12', plain,
% 1.19/1.37      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.19/1.37         ((v1_relat_1 @ X35)
% 1.19/1.37          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 1.19/1.37      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.19/1.37  thf('13', plain, ((v1_relat_1 @ sk_C)),
% 1.19/1.37      inference('sup-', [status(thm)], ['11', '12'])).
% 1.19/1.37  thf('14', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 1.19/1.37      inference('demod', [status(thm)], ['10', '13'])).
% 1.19/1.37  thf(t87_relat_1, axiom,
% 1.19/1.37    (![A:$i,B:$i]:
% 1.19/1.37     ( ( v1_relat_1 @ B ) =>
% 1.19/1.37       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 1.19/1.37  thf('15', plain,
% 1.19/1.37      (![X24 : $i, X25 : $i]:
% 1.19/1.37         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X24 @ X25)) @ X25)
% 1.19/1.37          | ~ (v1_relat_1 @ X24))),
% 1.19/1.37      inference('cnf', [status(esa)], [t87_relat_1])).
% 1.19/1.37  thf('16', plain,
% 1.19/1.37      (((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A) | ~ (v1_relat_1 @ sk_C))),
% 1.19/1.37      inference('sup+', [status(thm)], ['14', '15'])).
% 1.19/1.37  thf('17', plain, ((v1_relat_1 @ sk_C)),
% 1.19/1.37      inference('sup-', [status(thm)], ['11', '12'])).
% 1.19/1.37  thf('18', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 1.19/1.37      inference('demod', [status(thm)], ['16', '17'])).
% 1.19/1.37  thf(t167_relat_1, axiom,
% 1.19/1.37    (![A:$i,B:$i]:
% 1.19/1.37     ( ( v1_relat_1 @ B ) =>
% 1.19/1.37       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 1.19/1.37  thf('19', plain,
% 1.19/1.37      (![X13 : $i, X14 : $i]:
% 1.19/1.37         ((r1_tarski @ (k10_relat_1 @ X13 @ X14) @ (k1_relat_1 @ X13))
% 1.19/1.37          | ~ (v1_relat_1 @ X13))),
% 1.19/1.37      inference('cnf', [status(esa)], [t167_relat_1])).
% 1.19/1.37  thf(t1_xboole_1, axiom,
% 1.19/1.37    (![A:$i,B:$i,C:$i]:
% 1.19/1.37     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.19/1.37       ( r1_tarski @ A @ C ) ))).
% 1.19/1.37  thf('20', plain,
% 1.19/1.37      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.19/1.37         (~ (r1_tarski @ X3 @ X4)
% 1.19/1.37          | ~ (r1_tarski @ X4 @ X5)
% 1.19/1.37          | (r1_tarski @ X3 @ X5))),
% 1.19/1.37      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.19/1.37  thf('21', plain,
% 1.19/1.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.37         (~ (v1_relat_1 @ X0)
% 1.19/1.37          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ X2)
% 1.19/1.37          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ X2))),
% 1.19/1.37      inference('sup-', [status(thm)], ['19', '20'])).
% 1.19/1.37  thf('22', plain,
% 1.19/1.37      (![X0 : $i]:
% 1.19/1.37         ((r1_tarski @ (k10_relat_1 @ sk_C @ X0) @ sk_A)
% 1.19/1.37          | ~ (v1_relat_1 @ sk_C))),
% 1.19/1.37      inference('sup-', [status(thm)], ['18', '21'])).
% 1.19/1.37  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 1.19/1.37      inference('sup-', [status(thm)], ['11', '12'])).
% 1.19/1.37  thf('24', plain,
% 1.19/1.37      (![X0 : $i]: (r1_tarski @ (k10_relat_1 @ sk_C @ X0) @ sk_A)),
% 1.19/1.37      inference('demod', [status(thm)], ['22', '23'])).
% 1.19/1.37  thf(t217_relat_1, axiom,
% 1.19/1.37    (![A:$i,B:$i]:
% 1.19/1.37     ( ( r1_tarski @ A @ B ) =>
% 1.19/1.37       ( ![C:$i]:
% 1.19/1.37         ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ A ) ) =>
% 1.19/1.37           ( v4_relat_1 @ C @ B ) ) ) ))).
% 1.19/1.37  thf('25', plain,
% 1.19/1.37      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.19/1.37         (~ (v1_relat_1 @ X19)
% 1.19/1.37          | ~ (v4_relat_1 @ X19 @ X20)
% 1.19/1.37          | (v4_relat_1 @ X19 @ X21)
% 1.19/1.37          | ~ (r1_tarski @ X20 @ X21))),
% 1.19/1.37      inference('cnf', [status(esa)], [t217_relat_1])).
% 1.19/1.37  thf('26', plain,
% 1.19/1.37      (![X0 : $i, X1 : $i]:
% 1.19/1.37         ((v4_relat_1 @ X1 @ sk_A)
% 1.19/1.37          | ~ (v4_relat_1 @ X1 @ (k10_relat_1 @ sk_C @ X0))
% 1.19/1.37          | ~ (v1_relat_1 @ X1))),
% 1.19/1.37      inference('sup-', [status(thm)], ['24', '25'])).
% 1.19/1.37  thf('27', plain,
% 1.19/1.37      (![X0 : $i]:
% 1.19/1.37         (~ (v1_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_C @ X0)))
% 1.19/1.37          | (v4_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_C @ X0)) @ sk_A))),
% 1.19/1.37      inference('sup-', [status(thm)], ['5', '26'])).
% 1.19/1.37  thf('28', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 1.19/1.37      inference('cnf', [status(esa)], [fc24_relat_1])).
% 1.19/1.37  thf('29', plain,
% 1.19/1.37      (![X0 : $i]:
% 1.19/1.37         (v4_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_C @ X0)) @ sk_A)),
% 1.19/1.37      inference('demod', [status(thm)], ['27', '28'])).
% 1.19/1.37  thf('30', plain,
% 1.19/1.37      (![X17 : $i, X18 : $i]:
% 1.19/1.37         (((X17) = (k7_relat_1 @ X17 @ X18))
% 1.19/1.37          | ~ (v4_relat_1 @ X17 @ X18)
% 1.19/1.37          | ~ (v1_relat_1 @ X17))),
% 1.19/1.37      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.19/1.37  thf('31', plain,
% 1.19/1.37      (![X0 : $i]:
% 1.19/1.37         (~ (v1_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_C @ X0)))
% 1.19/1.37          | ((k6_relat_1 @ (k10_relat_1 @ sk_C @ X0))
% 1.19/1.37              = (k7_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_C @ X0)) @ sk_A)))),
% 1.19/1.37      inference('sup-', [status(thm)], ['29', '30'])).
% 1.19/1.37  thf('32', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 1.19/1.37      inference('cnf', [status(esa)], [fc24_relat_1])).
% 1.19/1.37  thf('33', plain,
% 1.19/1.37      (![X0 : $i]:
% 1.19/1.37         ((k6_relat_1 @ (k10_relat_1 @ sk_C @ X0))
% 1.19/1.37           = (k7_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_C @ X0)) @ sk_A))),
% 1.19/1.37      inference('demod', [status(thm)], ['31', '32'])).
% 1.19/1.37  thf(t148_relat_1, axiom,
% 1.19/1.37    (![A:$i,B:$i]:
% 1.19/1.37     ( ( v1_relat_1 @ B ) =>
% 1.19/1.37       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 1.19/1.37  thf('34', plain,
% 1.19/1.37      (![X11 : $i, X12 : $i]:
% 1.19/1.37         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 1.19/1.37          | ~ (v1_relat_1 @ X11))),
% 1.19/1.37      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.19/1.37  thf('35', plain,
% 1.19/1.37      (![X0 : $i]:
% 1.19/1.37         (((k2_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_C @ X0)))
% 1.19/1.37            = (k9_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_C @ X0)) @ sk_A))
% 1.19/1.37          | ~ (v1_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_C @ X0))))),
% 1.19/1.37      inference('sup+', [status(thm)], ['33', '34'])).
% 1.19/1.37  thf(t71_relat_1, axiom,
% 1.19/1.37    (![A:$i]:
% 1.19/1.37     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.19/1.37       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.19/1.37  thf('36', plain, (![X23 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 1.19/1.37      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.19/1.37  thf('37', plain,
% 1.19/1.37      (![X11 : $i, X12 : $i]:
% 1.19/1.37         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 1.19/1.37          | ~ (v1_relat_1 @ X11))),
% 1.19/1.37      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.19/1.37  thf(t43_funct_1, axiom,
% 1.19/1.37    (![A:$i,B:$i]:
% 1.19/1.37     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 1.19/1.37       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.19/1.37  thf('38', plain,
% 1.19/1.37      (![X33 : $i, X34 : $i]:
% 1.19/1.37         ((k5_relat_1 @ (k6_relat_1 @ X34) @ (k6_relat_1 @ X33))
% 1.19/1.37           = (k6_relat_1 @ (k3_xboole_0 @ X33 @ X34)))),
% 1.19/1.37      inference('cnf', [status(esa)], [t43_funct_1])).
% 1.19/1.37  thf(t94_relat_1, axiom,
% 1.19/1.37    (![A:$i,B:$i]:
% 1.19/1.37     ( ( v1_relat_1 @ B ) =>
% 1.19/1.37       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 1.19/1.37  thf('39', plain,
% 1.19/1.37      (![X26 : $i, X27 : $i]:
% 1.19/1.37         (((k7_relat_1 @ X27 @ X26) = (k5_relat_1 @ (k6_relat_1 @ X26) @ X27))
% 1.19/1.37          | ~ (v1_relat_1 @ X27))),
% 1.19/1.37      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.19/1.37  thf('40', plain,
% 1.19/1.37      (![X0 : $i, X1 : $i]:
% 1.19/1.37         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.19/1.37            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 1.19/1.37          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.19/1.37      inference('sup+', [status(thm)], ['38', '39'])).
% 1.19/1.37  thf('41', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 1.19/1.37      inference('cnf', [status(esa)], [fc24_relat_1])).
% 1.19/1.37  thf('42', plain,
% 1.19/1.37      (![X0 : $i, X1 : $i]:
% 1.19/1.37         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.19/1.37           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.19/1.37      inference('demod', [status(thm)], ['40', '41'])).
% 1.19/1.37  thf('43', plain, (![X23 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 1.19/1.37      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.19/1.37  thf('44', plain,
% 1.19/1.37      (![X0 : $i, X1 : $i]:
% 1.19/1.37         ((k2_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.19/1.37           = (k3_xboole_0 @ X1 @ X0))),
% 1.19/1.37      inference('sup+', [status(thm)], ['42', '43'])).
% 1.19/1.37  thf('45', plain,
% 1.19/1.37      (![X0 : $i, X1 : $i]:
% 1.19/1.37         (((k9_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X1 @ X0))
% 1.19/1.37          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.19/1.37      inference('sup+', [status(thm)], ['37', '44'])).
% 1.19/1.37  thf('46', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 1.19/1.37      inference('cnf', [status(esa)], [fc24_relat_1])).
% 1.19/1.37  thf('47', plain,
% 1.19/1.37      (![X0 : $i, X1 : $i]:
% 1.19/1.37         ((k9_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 1.19/1.37      inference('demod', [status(thm)], ['45', '46'])).
% 1.19/1.37  thf('48', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 1.19/1.37      inference('cnf', [status(esa)], [fc24_relat_1])).
% 1.19/1.37  thf('49', plain,
% 1.19/1.37      (![X0 : $i]:
% 1.19/1.37         ((k10_relat_1 @ sk_C @ X0)
% 1.19/1.37           = (k3_xboole_0 @ (k10_relat_1 @ sk_C @ X0) @ sk_A))),
% 1.19/1.37      inference('demod', [status(thm)], ['35', '36', '47', '48'])).
% 1.19/1.37  thf('50', plain,
% 1.19/1.37      (![X0 : $i]:
% 1.19/1.37         (((k10_relat_1 @ sk_C @ (k3_xboole_0 @ (k2_relat_1 @ sk_C) @ X0))
% 1.19/1.37            = (k3_xboole_0 @ (k10_relat_1 @ sk_C @ X0) @ sk_A))
% 1.19/1.37          | ~ (v1_relat_1 @ sk_C))),
% 1.19/1.37      inference('sup+', [status(thm)], ['4', '49'])).
% 1.19/1.37  thf('51', plain,
% 1.19/1.37      (![X0 : $i]:
% 1.19/1.37         ((k10_relat_1 @ sk_C @ X0)
% 1.19/1.37           = (k3_xboole_0 @ (k10_relat_1 @ sk_C @ X0) @ sk_A))),
% 1.19/1.37      inference('demod', [status(thm)], ['35', '36', '47', '48'])).
% 1.19/1.37  thf('52', plain, ((v1_relat_1 @ sk_C)),
% 1.19/1.37      inference('sup-', [status(thm)], ['11', '12'])).
% 1.19/1.37  thf('53', plain,
% 1.19/1.37      (![X0 : $i]:
% 1.19/1.37         ((k10_relat_1 @ sk_C @ (k3_xboole_0 @ (k2_relat_1 @ sk_C) @ X0))
% 1.19/1.37           = (k10_relat_1 @ sk_C @ X0))),
% 1.19/1.37      inference('demod', [status(thm)], ['50', '51', '52'])).
% 1.19/1.37  thf('54', plain,
% 1.19/1.37      (![X13 : $i, X14 : $i]:
% 1.19/1.37         ((r1_tarski @ (k10_relat_1 @ X13 @ X14) @ (k1_relat_1 @ X13))
% 1.19/1.37          | ~ (v1_relat_1 @ X13))),
% 1.19/1.37      inference('cnf', [status(esa)], [t167_relat_1])).
% 1.19/1.37  thf('55', plain,
% 1.19/1.37      (![X0 : $i, X2 : $i]:
% 1.19/1.37         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.19/1.37      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.19/1.37  thf('56', plain,
% 1.19/1.37      (![X0 : $i, X1 : $i]:
% 1.19/1.37         (~ (v1_relat_1 @ X0)
% 1.19/1.37          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 1.19/1.37          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 1.19/1.37      inference('sup-', [status(thm)], ['54', '55'])).
% 1.19/1.37  thf('57', plain,
% 1.19/1.37      (![X0 : $i]:
% 1.19/1.37         (~ (r1_tarski @ (k1_relat_1 @ sk_C) @ (k10_relat_1 @ sk_C @ X0))
% 1.19/1.37          | ((k1_relat_1 @ sk_C)
% 1.19/1.37              = (k10_relat_1 @ sk_C @ (k3_xboole_0 @ (k2_relat_1 @ sk_C) @ X0)))
% 1.19/1.37          | ~ (v1_relat_1 @ sk_C))),
% 1.19/1.37      inference('sup-', [status(thm)], ['53', '56'])).
% 1.19/1.37  thf('58', plain,
% 1.19/1.37      (![X0 : $i]:
% 1.19/1.37         ((k10_relat_1 @ sk_C @ (k3_xboole_0 @ (k2_relat_1 @ sk_C) @ X0))
% 1.19/1.37           = (k10_relat_1 @ sk_C @ X0))),
% 1.19/1.37      inference('demod', [status(thm)], ['50', '51', '52'])).
% 1.19/1.37  thf('59', plain, ((v1_relat_1 @ sk_C)),
% 1.19/1.37      inference('sup-', [status(thm)], ['11', '12'])).
% 1.19/1.37  thf('60', plain,
% 1.19/1.37      (![X0 : $i]:
% 1.19/1.37         (~ (r1_tarski @ (k1_relat_1 @ sk_C) @ (k10_relat_1 @ sk_C @ X0))
% 1.19/1.37          | ((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ X0)))),
% 1.19/1.37      inference('demod', [status(thm)], ['57', '58', '59'])).
% 1.19/1.37  thf('61', plain,
% 1.19/1.37      ((~ (v1_relat_1 @ sk_C)
% 1.19/1.37        | ((k1_relat_1 @ sk_C)
% 1.19/1.37            = (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))))),
% 1.19/1.37      inference('sup-', [status(thm)], ['3', '60'])).
% 1.19/1.37  thf('62', plain, ((v1_relat_1 @ sk_C)),
% 1.19/1.37      inference('sup-', [status(thm)], ['11', '12'])).
% 1.19/1.37  thf('63', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.19/1.37      inference('simplify', [status(thm)], ['0'])).
% 1.19/1.37  thf('64', plain,
% 1.19/1.37      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf(t13_relset_1, axiom,
% 1.19/1.37    (![A:$i,B:$i,C:$i,D:$i]:
% 1.19/1.37     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 1.19/1.37       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 1.19/1.37         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 1.19/1.37  thf('65', plain,
% 1.19/1.37      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i]:
% 1.19/1.37         (~ (r1_tarski @ (k1_relat_1 @ X55) @ X56)
% 1.19/1.37          | (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X57)))
% 1.19/1.37          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X57))))),
% 1.19/1.37      inference('cnf', [status(esa)], [t13_relset_1])).
% 1.19/1.37  thf('66', plain,
% 1.19/1.37      (![X0 : $i]:
% 1.19/1.37         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 1.19/1.37          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 1.19/1.37      inference('sup-', [status(thm)], ['64', '65'])).
% 1.19/1.37  thf('67', plain,
% 1.19/1.37      ((m1_subset_1 @ sk_C @ 
% 1.19/1.37        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))),
% 1.19/1.37      inference('sup-', [status(thm)], ['63', '66'])).
% 1.19/1.37  thf('68', plain,
% 1.19/1.37      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.19/1.37         ((v4_relat_1 @ X38 @ X39)
% 1.19/1.37          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 1.19/1.37      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.19/1.37  thf('69', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 1.19/1.37      inference('sup-', [status(thm)], ['67', '68'])).
% 1.19/1.37  thf('70', plain,
% 1.19/1.37      (![X17 : $i, X18 : $i]:
% 1.19/1.37         (((X17) = (k7_relat_1 @ X17 @ X18))
% 1.19/1.37          | ~ (v4_relat_1 @ X17 @ X18)
% 1.19/1.37          | ~ (v1_relat_1 @ X17))),
% 1.19/1.37      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.19/1.37  thf('71', plain,
% 1.19/1.37      ((~ (v1_relat_1 @ sk_C)
% 1.19/1.37        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))),
% 1.19/1.37      inference('sup-', [status(thm)], ['69', '70'])).
% 1.19/1.37  thf('72', plain, ((v1_relat_1 @ sk_C)),
% 1.19/1.37      inference('sup-', [status(thm)], ['11', '12'])).
% 1.19/1.37  thf('73', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 1.19/1.37      inference('demod', [status(thm)], ['71', '72'])).
% 1.19/1.37  thf('74', plain,
% 1.19/1.37      (![X11 : $i, X12 : $i]:
% 1.19/1.37         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 1.19/1.37          | ~ (v1_relat_1 @ X11))),
% 1.19/1.37      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.19/1.37  thf('75', plain,
% 1.19/1.37      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 1.19/1.37        | ~ (v1_relat_1 @ sk_C))),
% 1.19/1.37      inference('sup+', [status(thm)], ['73', '74'])).
% 1.19/1.37  thf('76', plain, ((v1_relat_1 @ sk_C)),
% 1.19/1.37      inference('sup-', [status(thm)], ['11', '12'])).
% 1.19/1.37  thf('77', plain,
% 1.19/1.37      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 1.19/1.37      inference('demod', [status(thm)], ['75', '76'])).
% 1.19/1.37  thf('78', plain, (![X29 : $i]: (v4_relat_1 @ (k6_relat_1 @ X29) @ X29)),
% 1.19/1.37      inference('cnf', [status(esa)], [fc24_relat_1])).
% 1.19/1.37  thf('79', plain,
% 1.19/1.37      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('80', plain,
% 1.19/1.37      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.19/1.37         ((v5_relat_1 @ X38 @ X40)
% 1.19/1.37          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 1.19/1.37      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.19/1.37  thf('81', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 1.19/1.37      inference('sup-', [status(thm)], ['79', '80'])).
% 1.19/1.37  thf(d19_relat_1, axiom,
% 1.19/1.37    (![A:$i,B:$i]:
% 1.19/1.37     ( ( v1_relat_1 @ B ) =>
% 1.19/1.37       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.19/1.37  thf('82', plain,
% 1.19/1.37      (![X9 : $i, X10 : $i]:
% 1.19/1.37         (~ (v5_relat_1 @ X9 @ X10)
% 1.19/1.37          | (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 1.19/1.37          | ~ (v1_relat_1 @ X9))),
% 1.19/1.37      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.19/1.37  thf('83', plain,
% 1.19/1.37      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 1.19/1.37      inference('sup-', [status(thm)], ['81', '82'])).
% 1.19/1.37  thf('84', plain, ((v1_relat_1 @ sk_C)),
% 1.19/1.37      inference('sup-', [status(thm)], ['11', '12'])).
% 1.19/1.37  thf('85', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 1.19/1.37      inference('demod', [status(thm)], ['83', '84'])).
% 1.19/1.37  thf('86', plain,
% 1.19/1.37      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.19/1.37         (~ (v1_relat_1 @ X19)
% 1.19/1.37          | ~ (v4_relat_1 @ X19 @ X20)
% 1.19/1.37          | (v4_relat_1 @ X19 @ X21)
% 1.19/1.37          | ~ (r1_tarski @ X20 @ X21))),
% 1.19/1.37      inference('cnf', [status(esa)], [t217_relat_1])).
% 1.19/1.37  thf('87', plain,
% 1.19/1.37      (![X0 : $i]:
% 1.19/1.37         ((v4_relat_1 @ X0 @ sk_B)
% 1.19/1.37          | ~ (v4_relat_1 @ X0 @ (k2_relat_1 @ sk_C))
% 1.19/1.37          | ~ (v1_relat_1 @ X0))),
% 1.19/1.37      inference('sup-', [status(thm)], ['85', '86'])).
% 1.19/1.37  thf('88', plain,
% 1.19/1.37      ((~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 1.19/1.37        | (v4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ sk_B))),
% 1.19/1.37      inference('sup-', [status(thm)], ['78', '87'])).
% 1.19/1.37  thf('89', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 1.19/1.37      inference('cnf', [status(esa)], [fc24_relat_1])).
% 1.19/1.37  thf('90', plain, ((v4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ sk_B)),
% 1.19/1.37      inference('demod', [status(thm)], ['88', '89'])).
% 1.19/1.37  thf('91', plain,
% 1.19/1.37      (![X17 : $i, X18 : $i]:
% 1.19/1.37         (((X17) = (k7_relat_1 @ X17 @ X18))
% 1.19/1.37          | ~ (v4_relat_1 @ X17 @ X18)
% 1.19/1.37          | ~ (v1_relat_1 @ X17))),
% 1.19/1.37      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.19/1.37  thf('92', plain,
% 1.19/1.37      ((~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 1.19/1.37        | ((k6_relat_1 @ (k2_relat_1 @ sk_C))
% 1.19/1.37            = (k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ sk_B)))),
% 1.19/1.37      inference('sup-', [status(thm)], ['90', '91'])).
% 1.19/1.37  thf('93', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 1.19/1.37      inference('cnf', [status(esa)], [fc24_relat_1])).
% 1.19/1.37  thf('94', plain,
% 1.19/1.37      (((k6_relat_1 @ (k2_relat_1 @ sk_C))
% 1.19/1.37         = (k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ sk_B))),
% 1.19/1.37      inference('demod', [status(thm)], ['92', '93'])).
% 1.19/1.37  thf('95', plain,
% 1.19/1.37      (![X0 : $i, X1 : $i]:
% 1.19/1.37         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.19/1.37           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.19/1.37      inference('demod', [status(thm)], ['40', '41'])).
% 1.19/1.37  thf('96', plain, (![X22 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 1.19/1.37      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.19/1.37  thf('97', plain,
% 1.19/1.37      (![X0 : $i, X1 : $i]:
% 1.19/1.37         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.19/1.37           = (k3_xboole_0 @ X1 @ X0))),
% 1.19/1.37      inference('sup+', [status(thm)], ['95', '96'])).
% 1.19/1.37  thf('98', plain,
% 1.19/1.37      (((k1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 1.19/1.37         = (k3_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_B))),
% 1.19/1.37      inference('sup+', [status(thm)], ['94', '97'])).
% 1.19/1.37  thf('99', plain, (![X22 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 1.19/1.37      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.19/1.37  thf('100', plain,
% 1.19/1.37      (((k2_relat_1 @ sk_C) = (k3_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_B))),
% 1.19/1.37      inference('demod', [status(thm)], ['98', '99'])).
% 1.19/1.37  thf('101', plain,
% 1.19/1.37      (![X15 : $i, X16 : $i]:
% 1.19/1.37         (((k10_relat_1 @ X15 @ X16)
% 1.19/1.37            = (k10_relat_1 @ X15 @ (k3_xboole_0 @ (k2_relat_1 @ X15) @ X16)))
% 1.19/1.37          | ~ (v1_relat_1 @ X15))),
% 1.19/1.37      inference('cnf', [status(esa)], [t168_relat_1])).
% 1.19/1.37  thf('102', plain,
% 1.19/1.37      ((((k10_relat_1 @ sk_C @ sk_B)
% 1.19/1.37          = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 1.19/1.37        | ~ (v1_relat_1 @ sk_C))),
% 1.19/1.37      inference('sup+', [status(thm)], ['100', '101'])).
% 1.19/1.37  thf('103', plain, ((v1_relat_1 @ sk_C)),
% 1.19/1.37      inference('sup-', [status(thm)], ['11', '12'])).
% 1.19/1.37  thf('104', plain,
% 1.19/1.37      (((k10_relat_1 @ sk_C @ sk_B)
% 1.19/1.37         = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 1.19/1.37      inference('demod', [status(thm)], ['102', '103'])).
% 1.19/1.37  thf('105', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_B))),
% 1.19/1.37      inference('demod', [status(thm)], ['61', '62', '77', '104'])).
% 1.19/1.37  thf('106', plain,
% 1.19/1.37      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 1.19/1.37          != (k2_relset_1 @ sk_A @ sk_B @ sk_C))
% 1.19/1.37        | ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 1.19/1.37            != (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf('107', plain,
% 1.19/1.37      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 1.19/1.37          != (k1_relset_1 @ sk_A @ sk_B @ sk_C)))
% 1.19/1.37         <= (~
% 1.19/1.37             (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 1.19/1.37                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 1.19/1.37      inference('split', [status(esa)], ['106'])).
% 1.19/1.37  thf('108', plain,
% 1.19/1.37      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf(redefinition_k8_relset_1, axiom,
% 1.19/1.37    (![A:$i,B:$i,C:$i,D:$i]:
% 1.19/1.37     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.19/1.37       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 1.19/1.37  thf('109', plain,
% 1.19/1.37      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 1.19/1.37         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53)))
% 1.19/1.37          | ((k8_relset_1 @ X52 @ X53 @ X51 @ X54) = (k10_relat_1 @ X51 @ X54)))),
% 1.19/1.37      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 1.19/1.37  thf('110', plain,
% 1.19/1.37      (![X0 : $i]:
% 1.19/1.37         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 1.19/1.37      inference('sup-', [status(thm)], ['108', '109'])).
% 1.19/1.37  thf('111', plain,
% 1.19/1.37      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf(redefinition_k1_relset_1, axiom,
% 1.19/1.37    (![A:$i,B:$i,C:$i]:
% 1.19/1.37     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.19/1.37       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.19/1.37  thf('112', plain,
% 1.19/1.37      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.19/1.37         (((k1_relset_1 @ X42 @ X43 @ X41) = (k1_relat_1 @ X41))
% 1.19/1.37          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43))))),
% 1.19/1.37      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.19/1.37  thf('113', plain,
% 1.19/1.37      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 1.19/1.37      inference('sup-', [status(thm)], ['111', '112'])).
% 1.19/1.37  thf('114', plain,
% 1.19/1.37      ((((k10_relat_1 @ sk_C @ sk_B) != (k1_relat_1 @ sk_C)))
% 1.19/1.37         <= (~
% 1.19/1.37             (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 1.19/1.37                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 1.19/1.37      inference('demod', [status(thm)], ['107', '110', '113'])).
% 1.19/1.37  thf('115', plain,
% 1.19/1.37      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf(redefinition_k7_relset_1, axiom,
% 1.19/1.37    (![A:$i,B:$i,C:$i,D:$i]:
% 1.19/1.37     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.19/1.37       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 1.19/1.37  thf('116', plain,
% 1.19/1.37      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 1.19/1.37         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 1.19/1.37          | ((k7_relset_1 @ X48 @ X49 @ X47 @ X50) = (k9_relat_1 @ X47 @ X50)))),
% 1.19/1.37      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.19/1.37  thf('117', plain,
% 1.19/1.37      (![X0 : $i]:
% 1.19/1.37         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 1.19/1.37      inference('sup-', [status(thm)], ['115', '116'])).
% 1.19/1.37  thf('118', plain,
% 1.19/1.37      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 1.19/1.37          != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 1.19/1.37         <= (~
% 1.19/1.37             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 1.19/1.37                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 1.19/1.37      inference('split', [status(esa)], ['106'])).
% 1.19/1.37  thf('119', plain,
% 1.19/1.37      ((((k9_relat_1 @ sk_C @ sk_A) != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 1.19/1.37         <= (~
% 1.19/1.37             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 1.19/1.37                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 1.19/1.37      inference('sup-', [status(thm)], ['117', '118'])).
% 1.19/1.37  thf('120', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 1.19/1.37      inference('demod', [status(thm)], ['10', '13'])).
% 1.19/1.37  thf('121', plain,
% 1.19/1.37      (![X11 : $i, X12 : $i]:
% 1.19/1.37         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 1.19/1.37          | ~ (v1_relat_1 @ X11))),
% 1.19/1.37      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.19/1.37  thf('122', plain,
% 1.19/1.37      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))
% 1.19/1.37        | ~ (v1_relat_1 @ sk_C))),
% 1.19/1.37      inference('sup+', [status(thm)], ['120', '121'])).
% 1.19/1.37  thf('123', plain, ((v1_relat_1 @ sk_C)),
% 1.19/1.37      inference('sup-', [status(thm)], ['11', '12'])).
% 1.19/1.37  thf('124', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 1.19/1.37      inference('demod', [status(thm)], ['122', '123'])).
% 1.19/1.37  thf('125', plain,
% 1.19/1.37      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.19/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.37  thf(redefinition_k2_relset_1, axiom,
% 1.19/1.37    (![A:$i,B:$i,C:$i]:
% 1.19/1.37     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.19/1.37       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.19/1.37  thf('126', plain,
% 1.19/1.37      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.19/1.37         (((k2_relset_1 @ X45 @ X46 @ X44) = (k2_relat_1 @ X44))
% 1.19/1.37          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46))))),
% 1.19/1.37      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.19/1.37  thf('127', plain,
% 1.19/1.37      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.19/1.37      inference('sup-', [status(thm)], ['125', '126'])).
% 1.19/1.37  thf('128', plain,
% 1.19/1.37      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 1.19/1.37         <= (~
% 1.19/1.37             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 1.19/1.37                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 1.19/1.37      inference('demod', [status(thm)], ['119', '124', '127'])).
% 1.19/1.37  thf('129', plain,
% 1.19/1.37      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 1.19/1.37          = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 1.19/1.37      inference('simplify', [status(thm)], ['128'])).
% 1.19/1.37  thf('130', plain,
% 1.19/1.37      (~
% 1.19/1.37       (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 1.19/1.37          = (k1_relset_1 @ sk_A @ sk_B @ sk_C))) | 
% 1.19/1.37       ~
% 1.19/1.37       (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 1.19/1.37          = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 1.19/1.37      inference('split', [status(esa)], ['106'])).
% 1.19/1.37  thf('131', plain,
% 1.19/1.37      (~
% 1.19/1.37       (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 1.19/1.37          = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 1.19/1.37      inference('sat_resolution*', [status(thm)], ['129', '130'])).
% 1.19/1.37  thf('132', plain, (((k10_relat_1 @ sk_C @ sk_B) != (k1_relat_1 @ sk_C))),
% 1.19/1.37      inference('simpl_trail', [status(thm)], ['114', '131'])).
% 1.19/1.37  thf('133', plain, ($false),
% 1.19/1.37      inference('simplify_reflect-', [status(thm)], ['105', '132'])).
% 1.19/1.37  
% 1.19/1.37  % SZS output end Refutation
% 1.19/1.37  
% 1.19/1.38  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
