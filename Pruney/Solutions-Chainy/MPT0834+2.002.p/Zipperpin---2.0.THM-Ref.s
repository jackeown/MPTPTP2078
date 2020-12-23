%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WZj03mwWRv

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:38 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 366 expanded)
%              Number of leaves         :   43 ( 131 expanded)
%              Depth                    :   19
%              Number of atoms          : 1183 (3819 expanded)
%              Number of equality atoms :   84 ( 260 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(fc24_relat_1,axiom,(
    ! [A: $i] :
      ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X23: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ X23 ) @ X23 ) ),
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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v5_relat_1 @ X32 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('7',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v1_relat_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('8',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['5','8'])).

thf(t217_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v4_relat_1 @ C @ A ) )
         => ( v4_relat_1 @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v4_relat_1 @ X17 @ X18 )
      | ( v4_relat_1 @ X17 @ X19 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t217_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ sk_B )
      | ~ ( v4_relat_1 @ X0 @ ( k2_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ( v4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf('13',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('14',plain,(
    v4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['12','13'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15
        = ( k7_relat_1 @ X15 @ X16 ) )
      | ~ ( v4_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ( ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('18',plain,
    ( ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) )
    = ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('20',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('21',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('22',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('23',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X28 ) @ ( k6_relat_1 @ X27 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('25',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('26',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) )
        = ( k9_relat_1 @ X9 @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('32',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('35',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['23','33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('37',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k10_relat_1 @ X13 @ X14 )
        = ( k10_relat_1 @ X13 @ ( k3_xboole_0 @ ( k2_relat_1 @ X13 ) @ X14 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X0 @ X1 )
        = ( k10_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
      = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['6','7'])).

thf('41',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('42',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X11 @ X12 ) @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ sk_C @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('47',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['6','7'])).

thf('48',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ sk_C @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('52',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k1_relset_1 @ X36 @ X37 @ X35 )
        = ( k1_relat_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('53',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('56',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( ( k7_relset_1 @ X42 @ X43 @ X41 @ X44 )
        = ( k9_relat_1 @ X41 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['49'])).

thf('59',plain,
    ( ( ( k9_relat_1 @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v4_relat_1 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('62',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15
        = ( k7_relat_1 @ X15 @ X16 ) )
      | ~ ( v4_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['6','7'])).

thf('66',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('68',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['6','7'])).

thf('70',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('72',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k2_relset_1 @ X39 @ X40 @ X38 )
        = ( k2_relat_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('73',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['59','70','73'])).

thf('75',plain,
    ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
     != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A )
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['49'])).

thf('77',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
 != ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['75','76'])).

thf('78',plain,(
    ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['54','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('80',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( ( k8_relset_1 @ X46 @ X47 @ X45 @ X48 )
        = ( k10_relat_1 @ X45 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ( k10_relat_1 @ sk_C @ sk_B )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['78','81'])).

thf('83',plain,(
    ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ sk_C @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['48','82'])).

thf('84',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('85',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('87',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X49 ) @ X50 )
      | ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X51 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v4_relat_1 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('91',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15
        = ( k7_relat_1 @ X15 @ X16 ) )
      | ~ ( v4_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('93',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['6','7'])).

thf('95',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('97',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['6','7'])).

thf('99',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['84'])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('101',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X25 @ ( k1_relat_1 @ X26 ) )
      | ( r1_tarski @ X25 @ ( k10_relat_1 @ X26 @ ( k9_relat_1 @ X26 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['99','102'])).

thf('104',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('105',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['6','7'])).

thf('106',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,(
    $false ),
    inference(demod,[status(thm)],['83','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WZj03mwWRv
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:47:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.36  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.39/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.56  % Solved by: fo/fo7.sh
% 0.39/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.56  % done 190 iterations in 0.107s
% 0.39/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.56  % SZS output start Refutation
% 0.39/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.56  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.39/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.56  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.39/0.56  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.39/0.56  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.39/0.56  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.39/0.56  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.39/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.56  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.39/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.56  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.39/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.39/0.56  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.39/0.56  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.39/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.56  thf(fc24_relat_1, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.39/0.56       ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.39/0.56       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.39/0.56  thf('0', plain, (![X23 : $i]: (v4_relat_1 @ (k6_relat_1 @ X23) @ X23)),
% 0.39/0.56      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.39/0.56  thf(t38_relset_1, conjecture,
% 0.39/0.56    (![A:$i,B:$i,C:$i]:
% 0.39/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.56       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.39/0.56         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.39/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.56        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.56          ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.39/0.56            ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) )),
% 0.39/0.56    inference('cnf.neg', [status(esa)], [t38_relset_1])).
% 0.39/0.56  thf('1', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(cc2_relset_1, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i]:
% 0.39/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.56       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.39/0.56  thf('2', plain,
% 0.39/0.56      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.39/0.56         ((v5_relat_1 @ X32 @ X34)
% 0.39/0.56          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.39/0.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.39/0.56  thf('3', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.39/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.56  thf(d19_relat_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( v1_relat_1 @ B ) =>
% 0.39/0.56       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.39/0.56  thf('4', plain,
% 0.39/0.56      (![X5 : $i, X6 : $i]:
% 0.39/0.56         (~ (v5_relat_1 @ X5 @ X6)
% 0.39/0.56          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.39/0.56          | ~ (v1_relat_1 @ X5))),
% 0.39/0.56      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.39/0.56  thf('5', plain,
% 0.39/0.56      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.39/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.39/0.56  thf('6', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(cc1_relset_1, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i]:
% 0.39/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.56       ( v1_relat_1 @ C ) ))).
% 0.39/0.56  thf('7', plain,
% 0.39/0.56      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.39/0.56         ((v1_relat_1 @ X29)
% 0.39/0.56          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.39/0.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.39/0.56  thf('8', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.56  thf('9', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.39/0.56      inference('demod', [status(thm)], ['5', '8'])).
% 0.39/0.56  thf(t217_relat_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( r1_tarski @ A @ B ) =>
% 0.39/0.56       ( ![C:$i]:
% 0.39/0.56         ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ A ) ) =>
% 0.39/0.56           ( v4_relat_1 @ C @ B ) ) ) ))).
% 0.39/0.56  thf('10', plain,
% 0.39/0.56      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.39/0.56         (~ (v1_relat_1 @ X17)
% 0.39/0.56          | ~ (v4_relat_1 @ X17 @ X18)
% 0.39/0.56          | (v4_relat_1 @ X17 @ X19)
% 0.39/0.56          | ~ (r1_tarski @ X18 @ X19))),
% 0.39/0.56      inference('cnf', [status(esa)], [t217_relat_1])).
% 0.39/0.56  thf('11', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((v4_relat_1 @ X0 @ sk_B)
% 0.39/0.56          | ~ (v4_relat_1 @ X0 @ (k2_relat_1 @ sk_C))
% 0.39/0.56          | ~ (v1_relat_1 @ X0))),
% 0.39/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.39/0.56  thf('12', plain,
% 0.39/0.56      ((~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.39/0.56        | (v4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ sk_B))),
% 0.39/0.56      inference('sup-', [status(thm)], ['0', '11'])).
% 0.39/0.56  thf('13', plain, (![X22 : $i]: (v1_relat_1 @ (k6_relat_1 @ X22))),
% 0.39/0.56      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.39/0.56  thf('14', plain, ((v4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ sk_B)),
% 0.39/0.56      inference('demod', [status(thm)], ['12', '13'])).
% 0.39/0.56  thf(t209_relat_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.39/0.56       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.39/0.56  thf('15', plain,
% 0.39/0.56      (![X15 : $i, X16 : $i]:
% 0.39/0.56         (((X15) = (k7_relat_1 @ X15 @ X16))
% 0.39/0.56          | ~ (v4_relat_1 @ X15 @ X16)
% 0.39/0.56          | ~ (v1_relat_1 @ X15))),
% 0.39/0.56      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.39/0.56  thf('16', plain,
% 0.39/0.56      ((~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.39/0.56        | ((k6_relat_1 @ (k2_relat_1 @ sk_C))
% 0.39/0.56            = (k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ sk_B)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.39/0.56  thf('17', plain, (![X22 : $i]: (v1_relat_1 @ (k6_relat_1 @ X22))),
% 0.39/0.56      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.39/0.56  thf('18', plain,
% 0.39/0.56      (((k6_relat_1 @ (k2_relat_1 @ sk_C))
% 0.39/0.56         = (k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ sk_B))),
% 0.39/0.56      inference('demod', [status(thm)], ['16', '17'])).
% 0.39/0.56  thf(t148_relat_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( v1_relat_1 @ B ) =>
% 0.39/0.56       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.39/0.56  thf('19', plain,
% 0.39/0.56      (![X7 : $i, X8 : $i]:
% 0.39/0.56         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 0.39/0.56          | ~ (v1_relat_1 @ X7))),
% 0.39/0.56      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.39/0.56  thf('20', plain,
% 0.39/0.56      ((((k2_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.39/0.56          = (k9_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ sk_B))
% 0.39/0.56        | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C))))),
% 0.39/0.56      inference('sup+', [status(thm)], ['18', '19'])).
% 0.39/0.56  thf(t71_relat_1, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.39/0.56       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.39/0.56  thf('21', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 0.39/0.56      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.39/0.56  thf('22', plain, (![X22 : $i]: (v1_relat_1 @ (k6_relat_1 @ X22))),
% 0.39/0.56      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.39/0.56  thf('23', plain,
% 0.39/0.56      (((k2_relat_1 @ sk_C)
% 0.39/0.56         = (k9_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ sk_B))),
% 0.39/0.56      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.39/0.56  thf(t43_funct_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.39/0.56       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.39/0.56  thf('24', plain,
% 0.39/0.56      (![X27 : $i, X28 : $i]:
% 0.39/0.56         ((k5_relat_1 @ (k6_relat_1 @ X28) @ (k6_relat_1 @ X27))
% 0.39/0.56           = (k6_relat_1 @ (k3_xboole_0 @ X27 @ X28)))),
% 0.39/0.56      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.39/0.56  thf('25', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 0.39/0.56      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.39/0.56  thf(t160_relat_1, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( v1_relat_1 @ A ) =>
% 0.39/0.56       ( ![B:$i]:
% 0.39/0.56         ( ( v1_relat_1 @ B ) =>
% 0.39/0.56           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.39/0.56             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.39/0.56  thf('26', plain,
% 0.39/0.56      (![X9 : $i, X10 : $i]:
% 0.39/0.56         (~ (v1_relat_1 @ X9)
% 0.39/0.56          | ((k2_relat_1 @ (k5_relat_1 @ X10 @ X9))
% 0.39/0.56              = (k9_relat_1 @ X9 @ (k2_relat_1 @ X10)))
% 0.39/0.56          | ~ (v1_relat_1 @ X10))),
% 0.39/0.56      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.39/0.56  thf('27', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         (((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.39/0.56            = (k9_relat_1 @ X1 @ X0))
% 0.39/0.56          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.39/0.56          | ~ (v1_relat_1 @ X1))),
% 0.39/0.56      inference('sup+', [status(thm)], ['25', '26'])).
% 0.39/0.56  thf('28', plain, (![X22 : $i]: (v1_relat_1 @ (k6_relat_1 @ X22))),
% 0.39/0.56      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.39/0.56  thf('29', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         (((k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.39/0.56            = (k9_relat_1 @ X1 @ X0))
% 0.39/0.56          | ~ (v1_relat_1 @ X1))),
% 0.39/0.56      inference('demod', [status(thm)], ['27', '28'])).
% 0.39/0.56  thf('30', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         (((k2_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.39/0.56            = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.39/0.56          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.39/0.56      inference('sup+', [status(thm)], ['24', '29'])).
% 0.39/0.56  thf('31', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 0.39/0.56      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.39/0.56  thf('32', plain, (![X22 : $i]: (v1_relat_1 @ (k6_relat_1 @ X22))),
% 0.39/0.56      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.39/0.56  thf('33', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         ((k3_xboole_0 @ X1 @ X0) = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.39/0.56      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.39/0.56  thf(commutativity_k3_xboole_0, axiom,
% 0.39/0.56    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.39/0.56  thf('34', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.56  thf('35', plain,
% 0.39/0.56      (((k2_relat_1 @ sk_C) = (k3_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C)))),
% 0.39/0.56      inference('demod', [status(thm)], ['23', '33', '34'])).
% 0.39/0.56  thf('36', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.56  thf(t168_relat_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( v1_relat_1 @ B ) =>
% 0.39/0.56       ( ( k10_relat_1 @ B @ A ) =
% 0.39/0.56         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 0.39/0.56  thf('37', plain,
% 0.39/0.56      (![X13 : $i, X14 : $i]:
% 0.39/0.56         (((k10_relat_1 @ X13 @ X14)
% 0.39/0.56            = (k10_relat_1 @ X13 @ (k3_xboole_0 @ (k2_relat_1 @ X13) @ X14)))
% 0.39/0.56          | ~ (v1_relat_1 @ X13))),
% 0.39/0.56      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.39/0.56  thf('38', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         (((k10_relat_1 @ X0 @ X1)
% 0.39/0.56            = (k10_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0))))
% 0.39/0.56          | ~ (v1_relat_1 @ X0))),
% 0.39/0.56      inference('sup+', [status(thm)], ['36', '37'])).
% 0.39/0.56  thf('39', plain,
% 0.39/0.56      ((((k10_relat_1 @ sk_C @ sk_B)
% 0.39/0.56          = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.39/0.56        | ~ (v1_relat_1 @ sk_C))),
% 0.39/0.56      inference('sup+', [status(thm)], ['35', '38'])).
% 0.39/0.56  thf('40', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.56  thf('41', plain,
% 0.39/0.56      (((k10_relat_1 @ sk_C @ sk_B)
% 0.39/0.56         = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 0.39/0.56      inference('demod', [status(thm)], ['39', '40'])).
% 0.39/0.56  thf(t167_relat_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( v1_relat_1 @ B ) =>
% 0.39/0.56       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.39/0.56  thf('42', plain,
% 0.39/0.56      (![X11 : $i, X12 : $i]:
% 0.39/0.56         ((r1_tarski @ (k10_relat_1 @ X11 @ X12) @ (k1_relat_1 @ X11))
% 0.39/0.56          | ~ (v1_relat_1 @ X11))),
% 0.39/0.56      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.39/0.56  thf(d10_xboole_0, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.56  thf('43', plain,
% 0.39/0.56      (![X2 : $i, X4 : $i]:
% 0.39/0.56         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.39/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.56  thf('44', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         (~ (v1_relat_1 @ X0)
% 0.39/0.56          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.39/0.56          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['42', '43'])).
% 0.39/0.56  thf('45', plain,
% 0.39/0.56      ((~ (r1_tarski @ (k1_relat_1 @ sk_C) @ (k10_relat_1 @ sk_C @ sk_B))
% 0.39/0.56        | ((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.39/0.56        | ~ (v1_relat_1 @ sk_C))),
% 0.39/0.56      inference('sup-', [status(thm)], ['41', '44'])).
% 0.39/0.56  thf('46', plain,
% 0.39/0.56      (((k10_relat_1 @ sk_C @ sk_B)
% 0.39/0.56         = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 0.39/0.56      inference('demod', [status(thm)], ['39', '40'])).
% 0.39/0.56  thf('47', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.56  thf('48', plain,
% 0.39/0.56      ((~ (r1_tarski @ (k1_relat_1 @ sk_C) @ (k10_relat_1 @ sk_C @ sk_B))
% 0.39/0.56        | ((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_B)))),
% 0.39/0.56      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.39/0.56  thf('49', plain,
% 0.39/0.56      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.39/0.56          != (k2_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.39/0.56        | ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.39/0.56            != (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('50', plain,
% 0.39/0.56      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.39/0.56          != (k1_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.39/0.56         <= (~
% 0.39/0.56             (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.39/0.56                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.39/0.56      inference('split', [status(esa)], ['49'])).
% 0.39/0.56  thf('51', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(redefinition_k1_relset_1, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i]:
% 0.39/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.39/0.56  thf('52', plain,
% 0.39/0.56      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.39/0.56         (((k1_relset_1 @ X36 @ X37 @ X35) = (k1_relat_1 @ X35))
% 0.39/0.56          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.39/0.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.39/0.56  thf('53', plain,
% 0.39/0.56      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.39/0.56      inference('sup-', [status(thm)], ['51', '52'])).
% 0.39/0.56  thf('54', plain,
% 0.39/0.56      ((((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B) != (k1_relat_1 @ sk_C)))
% 0.39/0.56         <= (~
% 0.39/0.56             (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.39/0.56                = (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.39/0.56      inference('demod', [status(thm)], ['50', '53'])).
% 0.39/0.56  thf('55', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(redefinition_k7_relset_1, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.56       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.39/0.56  thf('56', plain,
% 0.39/0.56      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.39/0.56         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 0.39/0.56          | ((k7_relset_1 @ X42 @ X43 @ X41 @ X44) = (k9_relat_1 @ X41 @ X44)))),
% 0.39/0.56      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.39/0.56  thf('57', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((k7_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.39/0.56      inference('sup-', [status(thm)], ['55', '56'])).
% 0.39/0.56  thf('58', plain,
% 0.39/0.56      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.39/0.56          != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.39/0.56         <= (~
% 0.39/0.56             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.39/0.56                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.39/0.56      inference('split', [status(esa)], ['49'])).
% 0.39/0.56  thf('59', plain,
% 0.39/0.56      ((((k9_relat_1 @ sk_C @ sk_A) != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.39/0.56         <= (~
% 0.39/0.56             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.39/0.56                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.39/0.56      inference('sup-', [status(thm)], ['57', '58'])).
% 0.39/0.56  thf('60', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('61', plain,
% 0.39/0.56      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.39/0.56         ((v4_relat_1 @ X32 @ X33)
% 0.39/0.56          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.39/0.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.39/0.56  thf('62', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.39/0.56      inference('sup-', [status(thm)], ['60', '61'])).
% 0.39/0.56  thf('63', plain,
% 0.39/0.56      (![X15 : $i, X16 : $i]:
% 0.39/0.56         (((X15) = (k7_relat_1 @ X15 @ X16))
% 0.39/0.56          | ~ (v4_relat_1 @ X15 @ X16)
% 0.39/0.56          | ~ (v1_relat_1 @ X15))),
% 0.39/0.56      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.39/0.56  thf('64', plain,
% 0.39/0.56      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['62', '63'])).
% 0.39/0.56  thf('65', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.56  thf('66', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.39/0.56      inference('demod', [status(thm)], ['64', '65'])).
% 0.39/0.56  thf('67', plain,
% 0.39/0.56      (![X7 : $i, X8 : $i]:
% 0.39/0.56         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 0.39/0.56          | ~ (v1_relat_1 @ X7))),
% 0.39/0.56      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.39/0.56  thf('68', plain,
% 0.39/0.56      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))
% 0.39/0.56        | ~ (v1_relat_1 @ sk_C))),
% 0.39/0.56      inference('sup+', [status(thm)], ['66', '67'])).
% 0.39/0.56  thf('69', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.56  thf('70', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.39/0.56      inference('demod', [status(thm)], ['68', '69'])).
% 0.39/0.56  thf('71', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(redefinition_k2_relset_1, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i]:
% 0.39/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.56       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.39/0.56  thf('72', plain,
% 0.39/0.56      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.39/0.56         (((k2_relset_1 @ X39 @ X40 @ X38) = (k2_relat_1 @ X38))
% 0.39/0.56          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 0.39/0.56      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.39/0.56  thf('73', plain,
% 0.39/0.56      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.39/0.56      inference('sup-', [status(thm)], ['71', '72'])).
% 0.39/0.56  thf('74', plain,
% 0.39/0.56      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.39/0.56         <= (~
% 0.39/0.56             (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.39/0.56                = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.39/0.56      inference('demod', [status(thm)], ['59', '70', '73'])).
% 0.39/0.56  thf('75', plain,
% 0.39/0.56      ((((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.39/0.56          = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.56      inference('simplify', [status(thm)], ['74'])).
% 0.39/0.56  thf('76', plain,
% 0.39/0.56      (~
% 0.39/0.56       (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.39/0.56          = (k1_relset_1 @ sk_A @ sk_B @ sk_C))) | 
% 0.39/0.56       ~
% 0.39/0.56       (((k7_relset_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.39/0.56          = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.56      inference('split', [status(esa)], ['49'])).
% 0.39/0.56  thf('77', plain,
% 0.39/0.56      (~
% 0.39/0.56       (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B)
% 0.39/0.56          = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.39/0.56      inference('sat_resolution*', [status(thm)], ['75', '76'])).
% 0.39/0.56  thf('78', plain,
% 0.39/0.56      (((k8_relset_1 @ sk_A @ sk_B @ sk_C @ sk_B) != (k1_relat_1 @ sk_C))),
% 0.39/0.56      inference('simpl_trail', [status(thm)], ['54', '77'])).
% 0.39/0.56  thf('79', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(redefinition_k8_relset_1, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.56       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.39/0.56  thf('80', plain,
% 0.39/0.56      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.39/0.56         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 0.39/0.56          | ((k8_relset_1 @ X46 @ X47 @ X45 @ X48) = (k10_relat_1 @ X45 @ X48)))),
% 0.39/0.56      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.39/0.56  thf('81', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((k8_relset_1 @ sk_A @ sk_B @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.39/0.56      inference('sup-', [status(thm)], ['79', '80'])).
% 0.39/0.56  thf('82', plain, (((k10_relat_1 @ sk_C @ sk_B) != (k1_relat_1 @ sk_C))),
% 0.39/0.56      inference('demod', [status(thm)], ['78', '81'])).
% 0.39/0.56  thf('83', plain,
% 0.39/0.56      (~ (r1_tarski @ (k1_relat_1 @ sk_C) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.39/0.56      inference('simplify_reflect-', [status(thm)], ['48', '82'])).
% 0.39/0.56  thf('84', plain,
% 0.39/0.56      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.39/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.56  thf('85', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.39/0.56      inference('simplify', [status(thm)], ['84'])).
% 0.39/0.56  thf('86', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(t13_relset_1, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.56     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.39/0.56       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 0.39/0.56         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.39/0.56  thf('87', plain,
% 0.39/0.56      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 0.39/0.56         (~ (r1_tarski @ (k1_relat_1 @ X49) @ X50)
% 0.39/0.56          | (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 0.39/0.56          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X51))))),
% 0.39/0.56      inference('cnf', [status(esa)], [t13_relset_1])).
% 0.39/0.56  thf('88', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.39/0.56          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.39/0.56      inference('sup-', [status(thm)], ['86', '87'])).
% 0.39/0.56  thf('89', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_C @ 
% 0.39/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['85', '88'])).
% 0.39/0.56  thf('90', plain,
% 0.39/0.56      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.39/0.56         ((v4_relat_1 @ X32 @ X33)
% 0.39/0.56          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.39/0.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.39/0.56  thf('91', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.39/0.56      inference('sup-', [status(thm)], ['89', '90'])).
% 0.39/0.56  thf('92', plain,
% 0.39/0.56      (![X15 : $i, X16 : $i]:
% 0.39/0.56         (((X15) = (k7_relat_1 @ X15 @ X16))
% 0.39/0.56          | ~ (v4_relat_1 @ X15 @ X16)
% 0.39/0.56          | ~ (v1_relat_1 @ X15))),
% 0.39/0.56      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.39/0.56  thf('93', plain,
% 0.39/0.56      ((~ (v1_relat_1 @ sk_C)
% 0.39/0.56        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))),
% 0.39/0.56      inference('sup-', [status(thm)], ['91', '92'])).
% 0.39/0.56  thf('94', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.56  thf('95', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.39/0.56      inference('demod', [status(thm)], ['93', '94'])).
% 0.39/0.56  thf('96', plain,
% 0.39/0.56      (![X7 : $i, X8 : $i]:
% 0.39/0.56         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 0.39/0.56          | ~ (v1_relat_1 @ X7))),
% 0.39/0.56      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.39/0.56  thf('97', plain,
% 0.39/0.56      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 0.39/0.56        | ~ (v1_relat_1 @ sk_C))),
% 0.39/0.56      inference('sup+', [status(thm)], ['95', '96'])).
% 0.39/0.56  thf('98', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.56  thf('99', plain,
% 0.39/0.56      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.39/0.56      inference('demod', [status(thm)], ['97', '98'])).
% 0.39/0.56  thf('100', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.39/0.56      inference('simplify', [status(thm)], ['84'])).
% 0.39/0.56  thf(t146_funct_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( v1_relat_1 @ B ) =>
% 0.39/0.56       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.39/0.56         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.39/0.56  thf('101', plain,
% 0.39/0.56      (![X25 : $i, X26 : $i]:
% 0.39/0.56         (~ (r1_tarski @ X25 @ (k1_relat_1 @ X26))
% 0.39/0.56          | (r1_tarski @ X25 @ (k10_relat_1 @ X26 @ (k9_relat_1 @ X26 @ X25)))
% 0.39/0.56          | ~ (v1_relat_1 @ X26))),
% 0.39/0.56      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.39/0.56  thf('102', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (~ (v1_relat_1 @ X0)
% 0.39/0.56          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.39/0.56             (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 0.39/0.56      inference('sup-', [status(thm)], ['100', '101'])).
% 0.39/0.56  thf('103', plain,
% 0.39/0.56      (((r1_tarski @ (k1_relat_1 @ sk_C) @ 
% 0.39/0.56         (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.39/0.56        | ~ (v1_relat_1 @ sk_C))),
% 0.39/0.56      inference('sup+', [status(thm)], ['99', '102'])).
% 0.39/0.56  thf('104', plain,
% 0.39/0.56      (((k10_relat_1 @ sk_C @ sk_B)
% 0.39/0.56         = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 0.39/0.56      inference('demod', [status(thm)], ['39', '40'])).
% 0.39/0.56  thf('105', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.56  thf('106', plain,
% 0.39/0.56      ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.39/0.56      inference('demod', [status(thm)], ['103', '104', '105'])).
% 0.39/0.56  thf('107', plain, ($false), inference('demod', [status(thm)], ['83', '106'])).
% 0.39/0.56  
% 0.39/0.56  % SZS output end Refutation
% 0.39/0.56  
% 0.42/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
