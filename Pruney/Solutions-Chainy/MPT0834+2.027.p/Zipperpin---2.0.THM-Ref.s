%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.J3FeZ2hiTa

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:41 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 615 expanded)
%              Number of leaves         :   45 ( 213 expanded)
%              Depth                    :   23
%              Number of atoms          : 1416 (6077 expanded)
%              Number of equality atoms :   93 ( 358 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

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
    ! [X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ X35 @ ( k1_relat_1 @ X36 ) )
      | ( r1_tarski @ X35 @ ( k10_relat_1 @ X36 @ ( k9_relat_1 @ X36 @ X35 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ( ( k10_relat_1 @ X21 @ X22 )
        = ( k10_relat_1 @ X21 @ ( k3_xboole_0 @ ( k2_relat_1 @ X21 ) @ X22 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf(fc24_relat_1,axiom,(
    ! [A: $i] :
      ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X33: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ X33 ) @ X33 ) ),
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
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( v4_relat_1 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ( X23
        = ( k7_relat_1 @ X23 @ X24 ) )
      | ~ ( v4_relat_1 @ X23 @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['10','15'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('17',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X30 @ X31 ) ) @ X31 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('18',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('20',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['18','19'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('21',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X19 @ X20 ) @ ( k1_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t217_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v4_relat_1 @ C @ A ) )
         => ( v4_relat_1 @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ~ ( v4_relat_1 @ X25 @ X26 )
      | ( v4_relat_1 @ X25 @ X27 )
      | ~ ( r1_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t217_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_relat_1 @ X1 @ sk_A )
      | ~ ( v4_relat_1 @ X1 @ ( k10_relat_1 @ sk_C @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_C @ X0 ) ) )
      | ( v4_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_C @ X0 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','28'])).

thf('30',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_C @ X0 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X23: $i,X24: $i] :
      ( ( X23
        = ( k7_relat_1 @ X23 @ X24 ) )
      | ~ ( v4_relat_1 @ X23 @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_C @ X0 ) ) )
      | ( ( k6_relat_1 @ ( k10_relat_1 @ sk_C @ X0 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_C @ X0 ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k6_relat_1 @ ( k10_relat_1 @ sk_C @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_C @ X0 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) )
        = ( k9_relat_1 @ X15 @ X16 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_C @ X0 ) ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_C @ X0 ) ) @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('38',plain,(
    ! [X29: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X38 ) @ ( k6_relat_1 @ X37 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('40',plain,(
    ! [X29: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('41',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X18 @ X17 ) )
        = ( k9_relat_1 @ X17 @ ( k2_relat_1 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X29: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('47',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C @ X0 )
      = ( k3_xboole_0 @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38','48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['4','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C @ X0 )
      = ( k3_xboole_0 @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38','48','49'])).

thf('53',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X19 @ X20 ) @ ( k1_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('56',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ sk_C @ X0 ) )
      | ( ( k1_relat_1 @ sk_C )
        = ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('60',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ sk_C @ X0 ) )
      | ( ( k1_relat_1 @ sk_C )
        = ( k10_relat_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['3','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('64',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('66',plain,(
    ! [X56: $i,X57: $i,X58: $i,X59: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X56 ) @ X57 )
      | ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X58 ) ) )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X58 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( v4_relat_1 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('70',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X23: $i,X24: $i] :
      ( ( X23
        = ( k7_relat_1 @ X23 @ X24 ) )
      | ~ ( v4_relat_1 @ X23 @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('72',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('74',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) )
        = ( k9_relat_1 @ X15 @ X16 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('76',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('78',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X33: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ X33 ) @ X33 ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( v5_relat_1 @ X39 @ X41 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('82',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['80','81'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('83',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v5_relat_1 @ X11 @ X12 )
      | ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('84',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('86',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ~ ( v4_relat_1 @ X25 @ X26 )
      | ( v4_relat_1 @ X25 @ X27 )
      | ~ ( r1_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t217_relat_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ sk_B )
      | ~ ( v4_relat_1 @ X0 @ ( k2_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ( v4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['79','88'])).

thf('90',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('91',plain,(
    v4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X23: $i,X24: $i] :
      ( ( X23
        = ( k7_relat_1 @ X23 @ X24 ) )
      | ~ ( v4_relat_1 @ X23 @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('93',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ( ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('95',plain,
    ( ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) )
    = ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) )
        = ( k9_relat_1 @ X15 @ X16 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('97',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X29: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('100',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('101',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k3_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['97','98','99','100'])).

thf('102',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k10_relat_1 @ X21 @ X22 )
        = ( k10_relat_1 @ X21 @ ( k3_xboole_0 @ ( k2_relat_1 @ X21 ) @ X22 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('103',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
      = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('105',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['62','63','78','105'])).

thf('107',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['107'])).

thf('109',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('110',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( ( k1_relset_1 @ X43 @ X44 @ X42 )
        = ( k1_relat_1 @ X42 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('111',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['108','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('114',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ( ( k7_relset_1 @ X49 @ X50 @ X48 @ X51 )
        = ( k9_relat_1 @ X48 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['107'])).

thf('117',plain,
    ( ( ( k9_relat_1 @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('119',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) )
        = ( k9_relat_1 @ X15 @ X16 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('120',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('122',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('124',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( ( k2_relset_1 @ X46 @ X47 @ X45 )
        = ( k2_relat_1 @ X45 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('125',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['117','122','125'])).

thf('127',plain,
    ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['107'])).

thf('129',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
 != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['127','128'])).

thf('130',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['112','129'])).

thf('131',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('132',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) )
      | ( ( k8_relset_1 @ X53 @ X54 @ X52 @ X55 )
        = ( k10_relat_1 @ X52 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ( k10_relat_1 @ sk_C @ sk_B )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['130','133'])).

thf('135',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['106','134'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.J3FeZ2hiTa
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:06:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.89/1.16  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.89/1.16  % Solved by: fo/fo7.sh
% 0.89/1.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.16  % done 1151 iterations in 0.705s
% 0.89/1.16  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.89/1.16  % SZS output start Refutation
% 0.89/1.16  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.89/1.16  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.89/1.16  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.89/1.16  thf(sk_C_type, type, sk_C: $i).
% 0.89/1.16  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.89/1.16  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.89/1.16  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.89/1.16  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.89/1.16  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.89/1.16  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.89/1.16  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.89/1.16  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.16  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.89/1.16  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.89/1.16  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.89/1.16  thf(sk_B_type, type, sk_B: $i).
% 0.89/1.16  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.89/1.16  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.89/1.16  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.89/1.16  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.89/1.16  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.89/1.16  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.89/1.16  thf(d10_xboole_0, axiom,
% 0.89/1.16    (![A:$i,B:$i]:
% 0.89/1.16     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.89/1.16  thf('0', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.89/1.16      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.89/1.16  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.89/1.16      inference('simplify', [status(thm)], ['0'])).
% 0.89/1.16  thf(t146_funct_1, axiom,
% 0.89/1.16    (![A:$i,B:$i]:
% 0.89/1.16     ( ( v1_relat_1 @ B ) =>
% 0.89/1.16       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.89/1.16         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.89/1.16  thf('2', plain,
% 0.89/1.16      (![X35 : $i, X36 : $i]:
% 0.89/1.16         (~ (r1_tarski @ X35 @ (k1_relat_1 @ X36))
% 0.89/1.16          | (r1_tarski @ X35 @ (k10_relat_1 @ X36 @ (k9_relat_1 @ X36 @ X35)))
% 0.89/1.16          | ~ (v1_relat_1 @ X36))),
% 0.89/1.16      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.89/1.16  thf('3', plain,
% 0.89/1.16      (![X0 : $i]:
% 0.89/1.16         (~ (v1_relat_1 @ X0)
% 0.89/1.16          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.89/1.16             (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 0.89/1.16      inference('sup-', [status(thm)], ['1', '2'])).
% 0.89/1.16  thf(t168_relat_1, axiom,
% 0.89/1.16    (![A:$i,B:$i]:
% 0.89/1.16     ( ( v1_relat_1 @ B ) =>
% 0.89/1.16       ( ( k10_relat_1 @ B @ A ) =
% 0.89/1.16         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 0.89/1.16  thf('4', plain,
% 0.89/1.16      (![X21 : $i, X22 : $i]:
% 0.89/1.16         (((k10_relat_1 @ X21 @ X22)
% 0.89/1.16            = (k10_relat_1 @ X21 @ (k3_xboole_0 @ (k2_relat_1 @ X21) @ X22)))
% 0.89/1.16          | ~ (v1_relat_1 @ X21))),
% 0.89/1.16      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.89/1.16  thf(fc24_relat_1, axiom,
% 0.89/1.16    (![A:$i]:
% 0.89/1.16     ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.89/1.16       ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.89/1.16       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.89/1.16  thf('5', plain, (![X33 : $i]: (v4_relat_1 @ (k6_relat_1 @ X33) @ X33)),
% 0.89/1.16      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.89/1.16  thf(t38_relset_1, conjecture,
% 0.89/1.16    (![A:$i,B:$i,C:$i]:
% 0.89/1.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.16       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.89/1.16         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.89/1.16  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.16    (~( ![A:$i,B:$i,C:$i]:
% 0.89/1.16        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.16          ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.89/1.16            ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) )),
% 0.89/1.16    inference('cnf.neg', [status(esa)], [t38_relset_1])).
% 0.89/1.16  thf('6', plain,
% 0.89/1.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.16  thf(cc2_relset_1, axiom,
% 0.89/1.16    (![A:$i,B:$i,C:$i]:
% 0.89/1.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.16       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.89/1.16  thf('7', plain,
% 0.89/1.16      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.89/1.16         ((v4_relat_1 @ X39 @ X40)
% 0.89/1.16          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 0.89/1.16      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.89/1.16  thf('8', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.89/1.16      inference('sup-', [status(thm)], ['6', '7'])).
% 0.89/1.16  thf(t209_relat_1, axiom,
% 0.89/1.16    (![A:$i,B:$i]:
% 0.89/1.16     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.89/1.16       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.89/1.16  thf('9', plain,
% 0.89/1.16      (![X23 : $i, X24 : $i]:
% 0.89/1.16         (((X23) = (k7_relat_1 @ X23 @ X24))
% 0.89/1.16          | ~ (v4_relat_1 @ X23 @ X24)
% 0.89/1.16          | ~ (v1_relat_1 @ X23))),
% 0.89/1.16      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.89/1.16  thf('10', plain,
% 0.89/1.16      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.89/1.16      inference('sup-', [status(thm)], ['8', '9'])).
% 0.89/1.16  thf('11', plain,
% 0.89/1.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.16  thf(cc2_relat_1, axiom,
% 0.89/1.16    (![A:$i]:
% 0.89/1.16     ( ( v1_relat_1 @ A ) =>
% 0.89/1.16       ( ![B:$i]:
% 0.89/1.16         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.89/1.16  thf('12', plain,
% 0.89/1.16      (![X9 : $i, X10 : $i]:
% 0.89/1.16         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.89/1.16          | (v1_relat_1 @ X9)
% 0.89/1.16          | ~ (v1_relat_1 @ X10))),
% 0.89/1.16      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.89/1.16  thf('13', plain,
% 0.89/1.16      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.89/1.16      inference('sup-', [status(thm)], ['11', '12'])).
% 0.89/1.16  thf(fc6_relat_1, axiom,
% 0.89/1.16    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.89/1.16  thf('14', plain,
% 0.89/1.16      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 0.89/1.16      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.89/1.16  thf('15', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.16      inference('demod', [status(thm)], ['13', '14'])).
% 0.89/1.16  thf('16', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.89/1.16      inference('demod', [status(thm)], ['10', '15'])).
% 0.89/1.16  thf(t87_relat_1, axiom,
% 0.89/1.16    (![A:$i,B:$i]:
% 0.89/1.16     ( ( v1_relat_1 @ B ) =>
% 0.89/1.16       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.89/1.16  thf('17', plain,
% 0.89/1.16      (![X30 : $i, X31 : $i]:
% 0.89/1.16         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X30 @ X31)) @ X31)
% 0.89/1.16          | ~ (v1_relat_1 @ X30))),
% 0.89/1.16      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.89/1.16  thf('18', plain,
% 0.89/1.16      (((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A) | ~ (v1_relat_1 @ sk_C))),
% 0.89/1.16      inference('sup+', [status(thm)], ['16', '17'])).
% 0.89/1.16  thf('19', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.16      inference('demod', [status(thm)], ['13', '14'])).
% 0.89/1.16  thf('20', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.89/1.16      inference('demod', [status(thm)], ['18', '19'])).
% 0.89/1.16  thf(t167_relat_1, axiom,
% 0.89/1.16    (![A:$i,B:$i]:
% 0.89/1.16     ( ( v1_relat_1 @ B ) =>
% 0.89/1.16       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.89/1.16  thf('21', plain,
% 0.89/1.16      (![X19 : $i, X20 : $i]:
% 0.89/1.16         ((r1_tarski @ (k10_relat_1 @ X19 @ X20) @ (k1_relat_1 @ X19))
% 0.89/1.16          | ~ (v1_relat_1 @ X19))),
% 0.89/1.16      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.89/1.16  thf(t1_xboole_1, axiom,
% 0.89/1.16    (![A:$i,B:$i,C:$i]:
% 0.89/1.16     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.89/1.16       ( r1_tarski @ A @ C ) ))).
% 0.89/1.16  thf('22', plain,
% 0.89/1.16      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.89/1.16         (~ (r1_tarski @ X3 @ X4)
% 0.89/1.16          | ~ (r1_tarski @ X4 @ X5)
% 0.89/1.16          | (r1_tarski @ X3 @ X5))),
% 0.89/1.16      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.89/1.16  thf('23', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.16         (~ (v1_relat_1 @ X0)
% 0.89/1.16          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ X2)
% 0.89/1.16          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ X2))),
% 0.89/1.16      inference('sup-', [status(thm)], ['21', '22'])).
% 0.89/1.16  thf('24', plain,
% 0.89/1.16      (![X0 : $i]:
% 0.89/1.16         ((r1_tarski @ (k10_relat_1 @ sk_C @ X0) @ sk_A)
% 0.89/1.16          | ~ (v1_relat_1 @ sk_C))),
% 0.89/1.16      inference('sup-', [status(thm)], ['20', '23'])).
% 0.89/1.16  thf('25', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.16      inference('demod', [status(thm)], ['13', '14'])).
% 0.89/1.16  thf('26', plain,
% 0.89/1.16      (![X0 : $i]: (r1_tarski @ (k10_relat_1 @ sk_C @ X0) @ sk_A)),
% 0.89/1.16      inference('demod', [status(thm)], ['24', '25'])).
% 0.89/1.16  thf(t217_relat_1, axiom,
% 0.89/1.16    (![A:$i,B:$i]:
% 0.89/1.16     ( ( r1_tarski @ A @ B ) =>
% 0.89/1.16       ( ![C:$i]:
% 0.89/1.16         ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ A ) ) =>
% 0.89/1.16           ( v4_relat_1 @ C @ B ) ) ) ))).
% 0.89/1.16  thf('27', plain,
% 0.89/1.16      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.89/1.16         (~ (v1_relat_1 @ X25)
% 0.89/1.16          | ~ (v4_relat_1 @ X25 @ X26)
% 0.89/1.16          | (v4_relat_1 @ X25 @ X27)
% 0.89/1.16          | ~ (r1_tarski @ X26 @ X27))),
% 0.89/1.16      inference('cnf', [status(esa)], [t217_relat_1])).
% 0.89/1.16  thf('28', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((v4_relat_1 @ X1 @ sk_A)
% 0.89/1.16          | ~ (v4_relat_1 @ X1 @ (k10_relat_1 @ sk_C @ X0))
% 0.89/1.16          | ~ (v1_relat_1 @ X1))),
% 0.89/1.16      inference('sup-', [status(thm)], ['26', '27'])).
% 0.89/1.16  thf('29', plain,
% 0.89/1.16      (![X0 : $i]:
% 0.89/1.16         (~ (v1_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_C @ X0)))
% 0.89/1.16          | (v4_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_C @ X0)) @ sk_A))),
% 0.89/1.16      inference('sup-', [status(thm)], ['5', '28'])).
% 0.89/1.16  thf('30', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 0.89/1.16      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.89/1.16  thf('31', plain,
% 0.89/1.16      (![X0 : $i]:
% 0.89/1.16         (v4_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_C @ X0)) @ sk_A)),
% 0.89/1.17      inference('demod', [status(thm)], ['29', '30'])).
% 0.89/1.17  thf('32', plain,
% 0.89/1.17      (![X23 : $i, X24 : $i]:
% 0.89/1.17         (((X23) = (k7_relat_1 @ X23 @ X24))
% 0.89/1.17          | ~ (v4_relat_1 @ X23 @ X24)
% 0.89/1.17          | ~ (v1_relat_1 @ X23))),
% 0.89/1.17      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.89/1.17  thf('33', plain,
% 0.89/1.17      (![X0 : $i]:
% 0.89/1.17         (~ (v1_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_C @ X0)))
% 0.89/1.17          | ((k6_relat_1 @ (k10_relat_1 @ sk_C @ X0))
% 0.89/1.17              = (k7_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_C @ X0)) @ sk_A)))),
% 0.89/1.17      inference('sup-', [status(thm)], ['31', '32'])).
% 0.89/1.17  thf('34', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 0.89/1.17      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.89/1.17  thf('35', plain,
% 0.89/1.17      (![X0 : $i]:
% 0.89/1.17         ((k6_relat_1 @ (k10_relat_1 @ sk_C @ X0))
% 0.89/1.17           = (k7_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_C @ X0)) @ sk_A))),
% 0.89/1.17      inference('demod', [status(thm)], ['33', '34'])).
% 0.89/1.17  thf(t148_relat_1, axiom,
% 0.89/1.17    (![A:$i,B:$i]:
% 0.89/1.17     ( ( v1_relat_1 @ B ) =>
% 0.89/1.17       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.89/1.17  thf('36', plain,
% 0.89/1.17      (![X15 : $i, X16 : $i]:
% 0.89/1.17         (((k2_relat_1 @ (k7_relat_1 @ X15 @ X16)) = (k9_relat_1 @ X15 @ X16))
% 0.89/1.17          | ~ (v1_relat_1 @ X15))),
% 0.89/1.17      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.89/1.17  thf('37', plain,
% 0.89/1.17      (![X0 : $i]:
% 0.89/1.17         (((k2_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_C @ X0)))
% 0.89/1.17            = (k9_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_C @ X0)) @ sk_A))
% 0.89/1.17          | ~ (v1_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_C @ X0))))),
% 0.89/1.17      inference('sup+', [status(thm)], ['35', '36'])).
% 0.89/1.17  thf(t71_relat_1, axiom,
% 0.89/1.17    (![A:$i]:
% 0.89/1.17     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.89/1.17       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.89/1.17  thf('38', plain, (![X29 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X29)) = (X29))),
% 0.89/1.17      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.89/1.17  thf(t43_funct_1, axiom,
% 0.89/1.17    (![A:$i,B:$i]:
% 0.89/1.17     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.89/1.17       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.89/1.17  thf('39', plain,
% 0.89/1.17      (![X37 : $i, X38 : $i]:
% 0.89/1.17         ((k5_relat_1 @ (k6_relat_1 @ X38) @ (k6_relat_1 @ X37))
% 0.89/1.17           = (k6_relat_1 @ (k3_xboole_0 @ X37 @ X38)))),
% 0.89/1.17      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.89/1.17  thf('40', plain, (![X29 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X29)) = (X29))),
% 0.89/1.17      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.89/1.17  thf(t160_relat_1, axiom,
% 0.89/1.17    (![A:$i]:
% 0.89/1.17     ( ( v1_relat_1 @ A ) =>
% 0.89/1.17       ( ![B:$i]:
% 0.89/1.17         ( ( v1_relat_1 @ B ) =>
% 0.89/1.17           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.89/1.17             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.89/1.17  thf('41', plain,
% 0.89/1.17      (![X17 : $i, X18 : $i]:
% 0.89/1.17         (~ (v1_relat_1 @ X17)
% 0.89/1.17          | ((k2_relat_1 @ (k5_relat_1 @ X18 @ X17))
% 0.89/1.17              = (k9_relat_1 @ X17 @ (k2_relat_1 @ X18)))
% 0.89/1.17          | ~ (v1_relat_1 @ X18))),
% 0.89/1.17      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.89/1.17  thf('42', plain,
% 0.89/1.17      (![X0 : $i, X1 : $i]:
% 0.89/1.17         (((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.89/1.17            = (k9_relat_1 @ X1 @ X0))
% 0.89/1.17          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.89/1.17          | ~ (v1_relat_1 @ X1))),
% 0.89/1.17      inference('sup+', [status(thm)], ['40', '41'])).
% 0.89/1.17  thf('43', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 0.89/1.17      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.89/1.17  thf('44', plain,
% 0.89/1.17      (![X0 : $i, X1 : $i]:
% 0.89/1.17         (((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.89/1.17            = (k9_relat_1 @ X1 @ X0))
% 0.89/1.17          | ~ (v1_relat_1 @ X1))),
% 0.89/1.17      inference('demod', [status(thm)], ['42', '43'])).
% 0.89/1.17  thf('45', plain,
% 0.89/1.17      (![X0 : $i, X1 : $i]:
% 0.89/1.17         (((k2_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.89/1.17            = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.89/1.17          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.89/1.17      inference('sup+', [status(thm)], ['39', '44'])).
% 0.89/1.17  thf('46', plain, (![X29 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X29)) = (X29))),
% 0.89/1.17      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.89/1.17  thf('47', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 0.89/1.17      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.89/1.17  thf('48', plain,
% 0.89/1.17      (![X0 : $i, X1 : $i]:
% 0.89/1.17         ((k3_xboole_0 @ X1 @ X0) = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.89/1.17      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.89/1.17  thf('49', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 0.89/1.17      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.89/1.17  thf('50', plain,
% 0.89/1.17      (![X0 : $i]:
% 0.89/1.17         ((k10_relat_1 @ sk_C @ X0)
% 0.89/1.17           = (k3_xboole_0 @ (k10_relat_1 @ sk_C @ X0) @ sk_A))),
% 0.89/1.17      inference('demod', [status(thm)], ['37', '38', '48', '49'])).
% 0.89/1.17  thf('51', plain,
% 0.89/1.17      (![X0 : $i]:
% 0.89/1.17         (((k10_relat_1 @ sk_C @ (k3_xboole_0 @ (k2_relat_1 @ sk_C) @ X0))
% 0.89/1.17            = (k3_xboole_0 @ (k10_relat_1 @ sk_C @ X0) @ sk_A))
% 0.89/1.17          | ~ (v1_relat_1 @ sk_C))),
% 0.89/1.17      inference('sup+', [status(thm)], ['4', '50'])).
% 0.89/1.17  thf('52', plain,
% 0.89/1.17      (![X0 : $i]:
% 0.89/1.17         ((k10_relat_1 @ sk_C @ X0)
% 0.89/1.17           = (k3_xboole_0 @ (k10_relat_1 @ sk_C @ X0) @ sk_A))),
% 0.89/1.17      inference('demod', [status(thm)], ['37', '38', '48', '49'])).
% 0.89/1.17  thf('53', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.17      inference('demod', [status(thm)], ['13', '14'])).
% 0.89/1.17  thf('54', plain,
% 0.89/1.17      (![X0 : $i]:
% 0.89/1.17         ((k10_relat_1 @ sk_C @ (k3_xboole_0 @ (k2_relat_1 @ sk_C) @ X0))
% 0.89/1.17           = (k10_relat_1 @ sk_C @ X0))),
% 0.89/1.17      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.89/1.17  thf('55', plain,
% 0.89/1.17      (![X19 : $i, X20 : $i]:
% 0.89/1.17         ((r1_tarski @ (k10_relat_1 @ X19 @ X20) @ (k1_relat_1 @ X19))
% 0.89/1.17          | ~ (v1_relat_1 @ X19))),
% 0.89/1.17      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.89/1.17  thf('56', plain,
% 0.89/1.17      (![X0 : $i, X2 : $i]:
% 0.89/1.17         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.89/1.17      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.89/1.17  thf('57', plain,
% 0.89/1.17      (![X0 : $i, X1 : $i]:
% 0.89/1.17         (~ (v1_relat_1 @ X0)
% 0.89/1.17          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.89/1.17          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 0.89/1.17      inference('sup-', [status(thm)], ['55', '56'])).
% 0.89/1.17  thf('58', plain,
% 0.89/1.17      (![X0 : $i]:
% 0.89/1.17         (~ (r1_tarski @ (k1_relat_1 @ sk_C) @ (k10_relat_1 @ sk_C @ X0))
% 0.89/1.17          | ((k1_relat_1 @ sk_C)
% 0.89/1.17              = (k10_relat_1 @ sk_C @ (k3_xboole_0 @ (k2_relat_1 @ sk_C) @ X0)))
% 0.89/1.17          | ~ (v1_relat_1 @ sk_C))),
% 0.89/1.17      inference('sup-', [status(thm)], ['54', '57'])).
% 0.89/1.17  thf('59', plain,
% 0.89/1.17      (![X0 : $i]:
% 0.89/1.17         ((k10_relat_1 @ sk_C @ (k3_xboole_0 @ (k2_relat_1 @ sk_C) @ X0))
% 0.89/1.17           = (k10_relat_1 @ sk_C @ X0))),
% 0.89/1.17      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.89/1.17  thf('60', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.17      inference('demod', [status(thm)], ['13', '14'])).
% 0.89/1.17  thf('61', plain,
% 0.89/1.17      (![X0 : $i]:
% 0.89/1.17         (~ (r1_tarski @ (k1_relat_1 @ sk_C) @ (k10_relat_1 @ sk_C @ X0))
% 0.89/1.17          | ((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ X0)))),
% 0.89/1.17      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.89/1.17  thf('62', plain,
% 0.89/1.17      ((~ (v1_relat_1 @ sk_C)
% 0.89/1.17        | ((k1_relat_1 @ sk_C)
% 0.89/1.17            = (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))))),
% 0.89/1.17      inference('sup-', [status(thm)], ['3', '61'])).
% 0.89/1.17  thf('63', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.17      inference('demod', [status(thm)], ['13', '14'])).
% 0.89/1.17  thf('64', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.89/1.17      inference('simplify', [status(thm)], ['0'])).
% 0.89/1.17  thf('65', plain,
% 0.89/1.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.17  thf(t13_relset_1, axiom,
% 0.89/1.17    (![A:$i,B:$i,C:$i,D:$i]:
% 0.89/1.17     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.89/1.17       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 0.89/1.17         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.89/1.17  thf('66', plain,
% 0.89/1.17      (![X56 : $i, X57 : $i, X58 : $i, X59 : $i]:
% 0.89/1.17         (~ (r1_tarski @ (k1_relat_1 @ X56) @ X57)
% 0.89/1.17          | (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X58)))
% 0.89/1.17          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X58))))),
% 0.89/1.17      inference('cnf', [status(esa)], [t13_relset_1])).
% 0.89/1.17  thf('67', plain,
% 0.89/1.17      (![X0 : $i]:
% 0.89/1.17         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.89/1.17          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.89/1.17      inference('sup-', [status(thm)], ['65', '66'])).
% 0.89/1.17  thf('68', plain,
% 0.89/1.17      ((m1_subset_1 @ sk_C @ 
% 0.89/1.17        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))),
% 0.89/1.17      inference('sup-', [status(thm)], ['64', '67'])).
% 0.89/1.17  thf('69', plain,
% 0.89/1.17      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.89/1.17         ((v4_relat_1 @ X39 @ X40)
% 0.89/1.17          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 0.89/1.17      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.89/1.17  thf('70', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.89/1.17      inference('sup-', [status(thm)], ['68', '69'])).
% 0.89/1.17  thf('71', plain,
% 0.89/1.17      (![X23 : $i, X24 : $i]:
% 0.89/1.17         (((X23) = (k7_relat_1 @ X23 @ X24))
% 0.89/1.17          | ~ (v4_relat_1 @ X23 @ X24)
% 0.89/1.17          | ~ (v1_relat_1 @ X23))),
% 0.89/1.17      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.89/1.17  thf('72', plain,
% 0.89/1.17      ((~ (v1_relat_1 @ sk_C)
% 0.89/1.17        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))),
% 0.89/1.17      inference('sup-', [status(thm)], ['70', '71'])).
% 0.89/1.17  thf('73', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.17      inference('demod', [status(thm)], ['13', '14'])).
% 0.89/1.17  thf('74', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.89/1.17      inference('demod', [status(thm)], ['72', '73'])).
% 0.89/1.17  thf('75', plain,
% 0.89/1.17      (![X15 : $i, X16 : $i]:
% 0.89/1.17         (((k2_relat_1 @ (k7_relat_1 @ X15 @ X16)) = (k9_relat_1 @ X15 @ X16))
% 0.89/1.17          | ~ (v1_relat_1 @ X15))),
% 0.89/1.17      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.89/1.17  thf('76', plain,
% 0.89/1.17      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 0.89/1.17        | ~ (v1_relat_1 @ sk_C))),
% 0.89/1.17      inference('sup+', [status(thm)], ['74', '75'])).
% 0.89/1.17  thf('77', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.17      inference('demod', [status(thm)], ['13', '14'])).
% 0.89/1.17  thf('78', plain,
% 0.89/1.17      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.89/1.17      inference('demod', [status(thm)], ['76', '77'])).
% 0.89/1.17  thf('79', plain, (![X33 : $i]: (v4_relat_1 @ (k6_relat_1 @ X33) @ X33)),
% 0.89/1.17      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.89/1.17  thf('80', plain,
% 0.89/1.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.17  thf('81', plain,
% 0.89/1.17      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.89/1.17         ((v5_relat_1 @ X39 @ X41)
% 0.89/1.17          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 0.89/1.17      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.89/1.17  thf('82', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.89/1.17      inference('sup-', [status(thm)], ['80', '81'])).
% 0.89/1.17  thf(d19_relat_1, axiom,
% 0.89/1.17    (![A:$i,B:$i]:
% 0.89/1.17     ( ( v1_relat_1 @ B ) =>
% 0.89/1.17       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.89/1.17  thf('83', plain,
% 0.89/1.17      (![X11 : $i, X12 : $i]:
% 0.89/1.17         (~ (v5_relat_1 @ X11 @ X12)
% 0.89/1.17          | (r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 0.89/1.17          | ~ (v1_relat_1 @ X11))),
% 0.89/1.17      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.89/1.17  thf('84', plain,
% 0.89/1.17      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.89/1.17      inference('sup-', [status(thm)], ['82', '83'])).
% 0.89/1.17  thf('85', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.17      inference('demod', [status(thm)], ['13', '14'])).
% 0.89/1.17  thf('86', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.89/1.17      inference('demod', [status(thm)], ['84', '85'])).
% 0.89/1.17  thf('87', plain,
% 0.89/1.17      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.89/1.17         (~ (v1_relat_1 @ X25)
% 0.89/1.17          | ~ (v4_relat_1 @ X25 @ X26)
% 0.89/1.17          | (v4_relat_1 @ X25 @ X27)
% 0.89/1.17          | ~ (r1_tarski @ X26 @ X27))),
% 0.89/1.17      inference('cnf', [status(esa)], [t217_relat_1])).
% 0.89/1.17  thf('88', plain,
% 0.89/1.17      (![X0 : $i]:
% 0.89/1.17         ((v4_relat_1 @ X0 @ sk_B)
% 0.89/1.17          | ~ (v4_relat_1 @ X0 @ (k2_relat_1 @ sk_C))
% 0.89/1.17          | ~ (v1_relat_1 @ X0))),
% 0.89/1.17      inference('sup-', [status(thm)], ['86', '87'])).
% 0.89/1.17  thf('89', plain,
% 0.89/1.17      ((~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.89/1.17        | (v4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ sk_B))),
% 0.89/1.17      inference('sup-', [status(thm)], ['79', '88'])).
% 0.89/1.17  thf('90', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 0.89/1.17      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.89/1.17  thf('91', plain, ((v4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ sk_B)),
% 0.89/1.17      inference('demod', [status(thm)], ['89', '90'])).
% 0.89/1.17  thf('92', plain,
% 0.89/1.17      (![X23 : $i, X24 : $i]:
% 0.89/1.17         (((X23) = (k7_relat_1 @ X23 @ X24))
% 0.89/1.17          | ~ (v4_relat_1 @ X23 @ X24)
% 0.89/1.17          | ~ (v1_relat_1 @ X23))),
% 0.89/1.17      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.89/1.17  thf('93', plain,
% 0.89/1.17      ((~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.89/1.17        | ((k6_relat_1 @ (k2_relat_1 @ sk_C))
% 0.89/1.17            = (k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ sk_B)))),
% 0.89/1.17      inference('sup-', [status(thm)], ['91', '92'])).
% 0.89/1.17  thf('94', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 0.89/1.17      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.89/1.17  thf('95', plain,
% 0.89/1.17      (((k6_relat_1 @ (k2_relat_1 @ sk_C))
% 0.89/1.17         = (k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ sk_B))),
% 0.89/1.17      inference('demod', [status(thm)], ['93', '94'])).
% 0.89/1.17  thf('96', plain,
% 0.89/1.17      (![X15 : $i, X16 : $i]:
% 0.89/1.17         (((k2_relat_1 @ (k7_relat_1 @ X15 @ X16)) = (k9_relat_1 @ X15 @ X16))
% 0.89/1.17          | ~ (v1_relat_1 @ X15))),
% 0.89/1.17      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.89/1.17  thf('97', plain,
% 0.89/1.17      ((((k2_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.89/1.17          = (k9_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ sk_B))
% 0.89/1.17        | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C))))),
% 0.89/1.17      inference('sup+', [status(thm)], ['95', '96'])).
% 0.89/1.17  thf('98', plain, (![X29 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X29)) = (X29))),
% 0.89/1.17      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.89/1.17  thf('99', plain,
% 0.89/1.17      (![X0 : $i, X1 : $i]:
% 0.89/1.17         ((k3_xboole_0 @ X1 @ X0) = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.89/1.17      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.89/1.17  thf('100', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 0.89/1.17      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.89/1.17  thf('101', plain,
% 0.89/1.17      (((k2_relat_1 @ sk_C) = (k3_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.89/1.17      inference('demod', [status(thm)], ['97', '98', '99', '100'])).
% 0.89/1.17  thf('102', plain,
% 0.89/1.17      (![X21 : $i, X22 : $i]:
% 0.89/1.17         (((k10_relat_1 @ X21 @ X22)
% 0.89/1.17            = (k10_relat_1 @ X21 @ (k3_xboole_0 @ (k2_relat_1 @ X21) @ X22)))
% 0.89/1.17          | ~ (v1_relat_1 @ X21))),
% 0.89/1.17      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.89/1.17  thf('103', plain,
% 0.89/1.17      ((((k10_relat_1 @ sk_C @ sk_B)
% 0.89/1.17          = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.89/1.17        | ~ (v1_relat_1 @ sk_C))),
% 0.89/1.17      inference('sup+', [status(thm)], ['101', '102'])).
% 0.89/1.17  thf('104', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.17      inference('demod', [status(thm)], ['13', '14'])).
% 0.89/1.17  thf('105', plain,
% 0.89/1.17      (((k10_relat_1 @ sk_C @ sk_B)
% 0.89/1.17         = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 0.89/1.17      inference('demod', [status(thm)], ['103', '104'])).
% 0.89/1.17  thf('106', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_B))),
% 0.89/1.17      inference('demod', [status(thm)], ['62', '63', '78', '105'])).
% 0.89/1.17  thf('107', plain,
% 0.89/1.17      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.89/1.17          != (k2_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.89/1.17        | ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.89/1.17            != (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.89/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.17  thf('108', plain,
% 0.89/1.17      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.89/1.17          != (k1_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.89/1.17         <= (~
% 0.89/1.17             (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.89/1.17                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.89/1.17      inference('split', [status(esa)], ['107'])).
% 0.89/1.17  thf('109', plain,
% 0.89/1.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.17  thf(redefinition_k1_relset_1, axiom,
% 0.89/1.17    (![A:$i,B:$i,C:$i]:
% 0.89/1.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.17       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.89/1.17  thf('110', plain,
% 0.89/1.17      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.89/1.17         (((k1_relset_1 @ X43 @ X44 @ X42) = (k1_relat_1 @ X42))
% 0.89/1.17          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44))))),
% 0.89/1.17      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.89/1.17  thf('111', plain,
% 0.89/1.17      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.89/1.17      inference('sup-', [status(thm)], ['109', '110'])).
% 0.89/1.17  thf('112', plain,
% 0.89/1.17      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B) != (k1_relat_1 @ sk_C)))
% 0.89/1.17         <= (~
% 0.89/1.17             (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.89/1.17                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.89/1.17      inference('demod', [status(thm)], ['108', '111'])).
% 0.89/1.17  thf('113', plain,
% 0.89/1.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.17  thf(redefinition_k7_relset_1, axiom,
% 0.89/1.17    (![A:$i,B:$i,C:$i,D:$i]:
% 0.89/1.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.17       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.89/1.17  thf('114', plain,
% 0.89/1.17      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 0.89/1.17         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 0.89/1.17          | ((k7_relset_1 @ X49 @ X50 @ X48 @ X51) = (k9_relat_1 @ X48 @ X51)))),
% 0.89/1.17      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.89/1.17  thf('115', plain,
% 0.89/1.17      (![X0 : $i]:
% 0.89/1.17         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.89/1.17      inference('sup-', [status(thm)], ['113', '114'])).
% 0.89/1.17  thf('116', plain,
% 0.89/1.17      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.89/1.17          != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.89/1.17         <= (~
% 0.89/1.17             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.89/1.17                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.89/1.17      inference('split', [status(esa)], ['107'])).
% 0.89/1.17  thf('117', plain,
% 0.89/1.17      ((((k9_relat_1 @ sk_C @ sk_A) != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.89/1.17         <= (~
% 0.89/1.17             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.89/1.17                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.89/1.17      inference('sup-', [status(thm)], ['115', '116'])).
% 0.89/1.17  thf('118', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.89/1.17      inference('demod', [status(thm)], ['10', '15'])).
% 0.89/1.17  thf('119', plain,
% 0.89/1.17      (![X15 : $i, X16 : $i]:
% 0.89/1.17         (((k2_relat_1 @ (k7_relat_1 @ X15 @ X16)) = (k9_relat_1 @ X15 @ X16))
% 0.89/1.17          | ~ (v1_relat_1 @ X15))),
% 0.89/1.17      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.89/1.17  thf('120', plain,
% 0.89/1.17      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))
% 0.89/1.17        | ~ (v1_relat_1 @ sk_C))),
% 0.89/1.17      inference('sup+', [status(thm)], ['118', '119'])).
% 0.89/1.17  thf('121', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.17      inference('demod', [status(thm)], ['13', '14'])).
% 0.89/1.17  thf('122', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.89/1.17      inference('demod', [status(thm)], ['120', '121'])).
% 0.89/1.17  thf('123', plain,
% 0.89/1.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.17  thf(redefinition_k2_relset_1, axiom,
% 0.89/1.17    (![A:$i,B:$i,C:$i]:
% 0.89/1.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.17       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.89/1.17  thf('124', plain,
% 0.89/1.17      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.89/1.17         (((k2_relset_1 @ X46 @ X47 @ X45) = (k2_relat_1 @ X45))
% 0.89/1.17          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47))))),
% 0.89/1.17      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.89/1.17  thf('125', plain,
% 0.89/1.17      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.89/1.17      inference('sup-', [status(thm)], ['123', '124'])).
% 0.89/1.17  thf('126', plain,
% 0.89/1.17      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.89/1.17         <= (~
% 0.89/1.17             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.89/1.17                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.89/1.17      inference('demod', [status(thm)], ['117', '122', '125'])).
% 0.89/1.17  thf('127', plain,
% 0.89/1.17      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.89/1.17          = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.89/1.17      inference('simplify', [status(thm)], ['126'])).
% 0.89/1.17  thf('128', plain,
% 0.89/1.17      (~
% 0.89/1.17       (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.89/1.17          = (k1_relset_1 @ sk_A @ sk_B @ sk_C))) | 
% 0.89/1.17       ~
% 0.89/1.17       (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.89/1.17          = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.89/1.17      inference('split', [status(esa)], ['107'])).
% 0.89/1.17  thf('129', plain,
% 0.89/1.17      (~
% 0.89/1.17       (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.89/1.17          = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.89/1.17      inference('sat_resolution*', [status(thm)], ['127', '128'])).
% 0.89/1.17  thf('130', plain,
% 0.89/1.17      (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B) != (k1_relat_1 @ sk_C))),
% 0.89/1.17      inference('simpl_trail', [status(thm)], ['112', '129'])).
% 0.89/1.17  thf('131', plain,
% 0.89/1.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.17  thf(redefinition_k8_relset_1, axiom,
% 0.89/1.17    (![A:$i,B:$i,C:$i,D:$i]:
% 0.89/1.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.17       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.89/1.17  thf('132', plain,
% 0.89/1.17      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 0.89/1.17         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54)))
% 0.89/1.17          | ((k8_relset_1 @ X53 @ X54 @ X52 @ X55) = (k10_relat_1 @ X52 @ X55)))),
% 0.89/1.17      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.89/1.17  thf('133', plain,
% 0.89/1.17      (![X0 : $i]:
% 0.89/1.17         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.89/1.17      inference('sup-', [status(thm)], ['131', '132'])).
% 0.89/1.17  thf('134', plain, (((k10_relat_1 @ sk_C @ sk_B) != (k1_relat_1 @ sk_C))),
% 0.89/1.17      inference('demod', [status(thm)], ['130', '133'])).
% 0.89/1.17  thf('135', plain, ($false),
% 0.89/1.17      inference('simplify_reflect-', [status(thm)], ['106', '134'])).
% 0.89/1.17  
% 0.89/1.17  % SZS output end Refutation
% 0.89/1.17  
% 0.89/1.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
