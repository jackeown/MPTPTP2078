%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.46ydRN5vYC

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 285 expanded)
%              Number of leaves         :   42 ( 101 expanded)
%              Depth                    :   13
%              Number of atoms          : 1084 (3475 expanded)
%              Number of equality atoms :   88 ( 243 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k3_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X27 @ X28 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_relset_1])).

thf('2',plain,(
    m1_subset_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X24 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('4',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('7',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) )
    = ( k1_relat_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ ( k1_relat_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(t162_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
        = B ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X15 ) @ X14 )
        = X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t162_funct_1])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X17 ) @ ( k6_relat_1 @ X16 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('11',plain,(
    ! [X13: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) )
        = ( k9_relat_1 @ X5 @ ( k2_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('14',plain,(
    ! [X2: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X13: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('18',plain,(
    ! [X2: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['9','19'])).

thf('21',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_relat_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) ) )
    = ( k1_relat_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('23',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( ( k1_relset_1 @ X45 @ X44 @ ( k3_relset_1 @ X44 @ X45 @ X46 ) )
        = ( k2_relset_1 @ X44 @ X45 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[t24_relset_1])).

thf('24',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) )
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('26',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k2_relset_1 @ X34 @ X35 @ X33 )
        = ( k2_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('27',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) )
    = ( k1_relat_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('30',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('32',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['21','30','31'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('34',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k10_relat_1 @ X7 @ X8 )
        = ( k10_relat_1 @ X7 @ ( k3_xboole_0 @ ( k2_relat_1 @ X7 ) @ X8 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X0 @ X1 )
        = ( k10_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
      = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('38',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('39',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10
        = ( k7_relat_1 @ X10 @ X11 ) )
      | ~ ( v4_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('43',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('44',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['41','44'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('46',plain,(
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

thf('47',plain,(
    ! [X9: $i] :
      ( ( ( k10_relat_1 @ X9 @ ( k2_relat_1 @ X9 ) )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_A ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['42','43'])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['42','43'])).

thf('52',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('53',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('54',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('55',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('56',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) )
        = ( k9_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('57',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['42','43'])).

thf('59',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['54','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['42','43'])).

thf('62',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['36','60','61'])).

thf('63',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['63'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('67',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('70',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( ( k7_relset_1 @ X37 @ X38 @ X36 @ X39 )
        = ( k9_relat_1 @ X36 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['63'])).

thf('73',plain,
    ( ( ( k9_relat_1 @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('75',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('76',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['63'])).

thf('79',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
 != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['77','78'])).

thf('80',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['68','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('82',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k8_relset_1 @ X41 @ X42 @ X40 @ X43 )
        = ( k10_relat_1 @ X40 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ( k10_relat_1 @ sk_C @ sk_B )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['80','83'])).

thf('85',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['62','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.46ydRN5vYC
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:26:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 110 iterations in 0.039s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.48  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.48  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.48  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.48  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.48  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.48  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.48  thf(t38_relset_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.20/0.48         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.48        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48          ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.20/0.48            ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t38_relset_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(dt_k3_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48       ( m1_subset_1 @
% 0.20/0.48         ( k3_relset_1 @ A @ B @ C ) @ 
% 0.20/0.48         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.48         ((m1_subset_1 @ (k3_relset_1 @ X27 @ X28 @ X29) @ 
% 0.20/0.48           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 0.20/0.48          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      ((m1_subset_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.48  thf(dt_k1_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.48         ((m1_subset_1 @ (k1_relset_1 @ X24 @ X25 @ X26) @ (k1_zfmisc_1 @ X24))
% 0.20/0.48          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      ((m1_subset_1 @ 
% 0.20/0.48        (k1_relset_1 @ sk_B @ sk_A @ (k3_relset_1 @ sk_A @ sk_B @ sk_C)) @ 
% 0.20/0.48        (k1_zfmisc_1 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      ((m1_subset_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.48  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.48         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 0.20/0.48          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (((k1_relset_1 @ sk_B @ sk_A @ (k3_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.48         = (k1_relat_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      ((m1_subset_1 @ (k1_relat_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C)) @ 
% 0.20/0.48        (k1_zfmisc_1 @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['4', '7'])).
% 0.20/0.48  thf(t162_funct_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48       ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ))).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i]:
% 0.20/0.48         (((k9_relat_1 @ (k6_relat_1 @ X15) @ X14) = (X14))
% 0.20/0.48          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t162_funct_1])).
% 0.20/0.48  thf(t43_funct_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.20/0.48       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X16 : $i, X17 : $i]:
% 0.20/0.48         ((k5_relat_1 @ (k6_relat_1 @ X17) @ (k6_relat_1 @ X16))
% 0.20/0.48           = (k6_relat_1 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.20/0.48  thf(t71_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.20/0.48       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.48  thf('11', plain, (![X13 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.20/0.48      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.48  thf(t160_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( v1_relat_1 @ B ) =>
% 0.20/0.48           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.20/0.48             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X5)
% 0.20/0.48          | ((k2_relat_1 @ (k5_relat_1 @ X6 @ X5))
% 0.20/0.48              = (k9_relat_1 @ X5 @ (k2_relat_1 @ X6)))
% 0.20/0.48          | ~ (v1_relat_1 @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.20/0.48            = (k9_relat_1 @ X1 @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ X1))),
% 0.20/0.48      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.48  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.20/0.48  thf('14', plain, (![X2 : $i]: (v1_relat_1 @ (k6_relat_1 @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.20/0.48            = (k9_relat_1 @ X1 @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ X1))),
% 0.20/0.48      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((k2_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.20/0.48            = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['10', '15'])).
% 0.20/0.48  thf('17', plain, (![X13 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.20/0.48      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.48  thf('18', plain, (![X2 : $i]: (v1_relat_1 @ (k6_relat_1 @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((k3_xboole_0 @ X1 @ X0) = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i]:
% 0.20/0.48         (((k3_xboole_0 @ X15 @ X14) = (X14))
% 0.20/0.48          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.20/0.48      inference('demod', [status(thm)], ['9', '19'])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (((k3_xboole_0 @ sk_B @ (k1_relat_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.48         = (k1_relat_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['8', '20'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t24_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48       ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.20/0.48           ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.20/0.48         ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.20/0.48           ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.20/0.48         (((k1_relset_1 @ X45 @ X44 @ (k3_relset_1 @ X44 @ X45 @ X46))
% 0.20/0.48            = (k2_relset_1 @ X44 @ X45 @ X46))
% 0.20/0.48          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45))))),
% 0.20/0.48      inference('cnf', [status(esa)], [t24_relset_1])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (((k1_relset_1 @ sk_B @ sk_A @ (k3_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.48         = (k2_relset_1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.20/0.48         (((k2_relset_1 @ X34 @ X35 @ X33) = (k2_relat_1 @ X33))
% 0.20/0.48          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (((k1_relset_1 @ sk_B @ sk_A @ (k3_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.48         = (k2_relat_1 @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['24', '27'])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (((k1_relset_1 @ sk_B @ sk_A @ (k3_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.48         = (k1_relat_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['28', '29'])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['28', '29'])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (((k3_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['21', '30', '31'])).
% 0.20/0.48  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.48  thf(t168_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( ( k10_relat_1 @ B @ A ) =
% 0.20/0.48         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i]:
% 0.20/0.48         (((k10_relat_1 @ X7 @ X8)
% 0.20/0.48            = (k10_relat_1 @ X7 @ (k3_xboole_0 @ (k2_relat_1 @ X7) @ X8)))
% 0.20/0.48          | ~ (v1_relat_1 @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((k10_relat_1 @ X0 @ X1)
% 0.20/0.48            = (k10_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0))))
% 0.20/0.48          | ~ (v1_relat_1 @ X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['33', '34'])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      ((((k10_relat_1 @ sk_C @ sk_B)
% 0.20/0.48          = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.20/0.48        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.48      inference('sup+', [status(thm)], ['32', '35'])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(cc2_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.48         ((v4_relat_1 @ X21 @ X22)
% 0.20/0.48          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.48  thf('39', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.20/0.48      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.48  thf(t209_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.48       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i]:
% 0.20/0.48         (((X10) = (k7_relat_1 @ X10 @ X11))
% 0.20/0.48          | ~ (v4_relat_1 @ X10 @ X11)
% 0.20/0.48          | ~ (v1_relat_1 @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(cc1_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48       ( v1_relat_1 @ C ) ))).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.48         ((v1_relat_1 @ X18)
% 0.20/0.48          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.48  thf('44', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.48      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.48  thf('45', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['41', '44'])).
% 0.20/0.48  thf(t148_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.48  thf('46', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i]:
% 0.20/0.48         (((k2_relat_1 @ (k7_relat_1 @ X3 @ X4)) = (k9_relat_1 @ X3 @ X4))
% 0.20/0.48          | ~ (v1_relat_1 @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.48  thf(t169_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      (![X9 : $i]:
% 0.20/0.48         (((k10_relat_1 @ X9 @ (k2_relat_1 @ X9)) = (k1_relat_1 @ X9))
% 0.20/0.48          | ~ (v1_relat_1 @ X9))),
% 0.20/0.48      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.20/0.48  thf('48', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.20/0.48            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.20/0.48          | ~ (v1_relat_1 @ X1)
% 0.20/0.48          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['46', '47'])).
% 0.20/0.48  thf('49', plain,
% 0.20/0.48      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.48        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.48        | ((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ 
% 0.20/0.48            (k9_relat_1 @ sk_C @ sk_A))
% 0.20/0.48            = (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['45', '48'])).
% 0.20/0.48  thf('50', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.48      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.48  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.48      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.48  thf('52', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['41', '44'])).
% 0.20/0.48  thf('53', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['41', '44'])).
% 0.20/0.48  thf('54', plain,
% 0.20/0.48      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) = (k1_relat_1 @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 0.20/0.48  thf('55', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['41', '44'])).
% 0.20/0.48  thf('56', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i]:
% 0.20/0.48         (((k2_relat_1 @ (k7_relat_1 @ X3 @ X4)) = (k9_relat_1 @ X3 @ X4))
% 0.20/0.48          | ~ (v1_relat_1 @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.48  thf('57', plain,
% 0.20/0.48      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))
% 0.20/0.48        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.48      inference('sup+', [status(thm)], ['55', '56'])).
% 0.20/0.48  thf('58', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.48      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.48  thf('59', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['57', '58'])).
% 0.20/0.48  thf('60', plain,
% 0.20/0.48      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['54', '59'])).
% 0.20/0.48  thf('61', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.48      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.48  thf('62', plain, (((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['36', '60', '61'])).
% 0.20/0.48  thf('63', plain,
% 0.20/0.48      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.48          != (k2_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.48        | ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.20/0.48            != (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('64', plain,
% 0.20/0.48      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.20/0.48          != (k1_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.20/0.48                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.48      inference('split', [status(esa)], ['63'])).
% 0.20/0.48  thf('65', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('66', plain,
% 0.20/0.48      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.48         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 0.20/0.48          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.48  thf('67', plain,
% 0.20/0.48      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['65', '66'])).
% 0.20/0.48  thf('68', plain,
% 0.20/0.48      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B) != (k1_relat_1 @ sk_C)))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.20/0.48                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.48      inference('demod', [status(thm)], ['64', '67'])).
% 0.20/0.48  thf('69', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(redefinition_k7_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.20/0.48  thf('70', plain,
% 0.20/0.48      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.20/0.48          | ((k7_relset_1 @ X37 @ X38 @ X36 @ X39) = (k9_relat_1 @ X36 @ X39)))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.20/0.48  thf('71', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.48  thf('72', plain,
% 0.20/0.48      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.48          != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.48                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.48      inference('split', [status(esa)], ['63'])).
% 0.20/0.48  thf('73', plain,
% 0.20/0.48      ((((k9_relat_1 @ sk_C @ sk_A) != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.48                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['71', '72'])).
% 0.20/0.48  thf('74', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['57', '58'])).
% 0.20/0.48  thf('75', plain,
% 0.20/0.48      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.48  thf('76', plain,
% 0.20/0.48      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.48                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.20/0.48      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.20/0.48  thf('77', plain,
% 0.20/0.48      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.48          = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['76'])).
% 0.20/0.48  thf('78', plain,
% 0.20/0.48      (~
% 0.20/0.48       (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.20/0.48          = (k1_relset_1 @ sk_A @ sk_B @ sk_C))) | 
% 0.20/0.48       ~
% 0.20/0.48       (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.48          = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.48      inference('split', [status(esa)], ['63'])).
% 0.20/0.48  thf('79', plain,
% 0.20/0.48      (~
% 0.20/0.48       (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.20/0.48          = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['77', '78'])).
% 0.20/0.48  thf('80', plain,
% 0.20/0.48      (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B) != (k1_relat_1 @ sk_C))),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['68', '79'])).
% 0.20/0.48  thf('81', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(redefinition_k8_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.20/0.48  thf('82', plain,
% 0.20/0.48      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.20/0.48          | ((k8_relset_1 @ X41 @ X42 @ X40 @ X43) = (k10_relat_1 @ X40 @ X43)))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.48  thf('83', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['81', '82'])).
% 0.20/0.48  thf('84', plain, (((k10_relat_1 @ sk_C @ sk_B) != (k1_relat_1 @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['80', '83'])).
% 0.20/0.48  thf('85', plain, ($false),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['62', '84'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
